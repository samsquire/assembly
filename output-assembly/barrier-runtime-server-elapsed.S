
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
  
  for (int x = 0 ; x < external_threads; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
    25df:	45 31 f6             	xor    %r14d,%r14d
int main() {
    25e2:	41 55                	push   %r13
    25e4:	41 54                	push   %r12
    25e6:	55                   	push   %rbp
    25e7:	53                   	push   %rbx
    25e8:	48 83 ec 68          	sub    $0x68,%rsp
    25ec:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    25f5:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    25fa:	31 c0                	xor    %eax,%eax
    25fc:	e8 cf fc ff ff       	call   22d0 <puts@plt>
    2601:	bf 0a 00 00 00       	mov    $0xa,%edi
    2606:	e8 b5 fc ff ff       	call   22c0 <putchar@plt>
    260b:	48 8d 3d 20 3c 00 00 	lea    0x3c20(%rip),%rdi        # 6232 <_IO_stdin_used+0x232>
    2612:	e8 b9 fc ff ff       	call   22d0 <puts@plt>
    2617:	ba 06 00 00 00       	mov    $0x6,%edx
    261c:	48 8d 35 2b 3c 00 00 	lea    0x3c2b(%rip),%rsi        # 624e <_IO_stdin_used+0x24e>
    2623:	31 c0                	xor    %eax,%eax
    2625:	bf 01 00 00 00       	mov    $0x1,%edi
    262a:	e8 01 fe ff ff       	call   2430 <__printf_chk@plt>
    262f:	ba 09 00 00 00       	mov    $0x9,%edx
    2634:	48 8d 35 2d 3c 00 00 	lea    0x3c2d(%rip),%rsi        # 6268 <_IO_stdin_used+0x268>
    263b:	31 c0                	xor    %eax,%eax
    263d:	bf 01 00 00 00       	mov    $0x1,%edi
    2642:	e8 e9 fd ff ff       	call   2430 <__printf_chk@plt>
    2647:	ba 01 00 00 00       	mov    $0x1,%edx
    264c:	48 8d 35 29 3c 00 00 	lea    0x3c29(%rip),%rsi        # 627c <_IO_stdin_used+0x27c>
    2653:	31 c0                	xor    %eax,%eax
    2655:	bf 01 00 00 00       	mov    $0x1,%edi
    265a:	e8 d1 fd ff ff       	call   2430 <__printf_chk@plt>
    265f:	ba 01 00 00 00       	mov    $0x1,%edx
    2664:	48 8d 35 22 3c 00 00 	lea    0x3c22(%rip),%rsi        # 628d <_IO_stdin_used+0x28d>
    266b:	31 c0                	xor    %eax,%eax
    266d:	bf 01 00 00 00       	mov    $0x1,%edi
    2672:	e8 b9 fd ff ff       	call   2430 <__printf_chk@plt>
    2677:	ba 01 00 00 00       	mov    $0x1,%edx
    267c:	48 8d 35 22 3c 00 00 	lea    0x3c22(%rip),%rsi        # 62a5 <_IO_stdin_used+0x2a5>
    2683:	31 c0                	xor    %eax,%eax
    2685:	bf 01 00 00 00       	mov    $0x1,%edi
    268a:	e8 a1 fd ff ff       	call   2430 <__printf_chk@plt>
    268f:	ba 01 00 00 00       	mov    $0x1,%edx
    2694:	48 8d 35 8d 3e 00 00 	lea    0x3e8d(%rip),%rsi        # 6528 <_IO_stdin_used+0x528>
    269b:	31 c0                	xor    %eax,%eax
    269d:	bf 01 00 00 00       	mov    $0x1,%edi
    26a2:	e8 89 fd ff ff       	call   2430 <__printf_chk@plt>
    26a7:	ba 01 00 00 00       	mov    $0x1,%edx
    26ac:	48 8d 35 a5 3e 00 00 	lea    0x3ea5(%rip),%rsi        # 6558 <_IO_stdin_used+0x558>
    26b3:	31 c0                	xor    %eax,%eax
    26b5:	bf 01 00 00 00       	mov    $0x1,%edi
    26ba:	e8 71 fd ff ff       	call   2430 <__printf_chk@plt>
    26bf:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    26c4:	48 8d 35 f6 3b 00 00 	lea    0x3bf6(%rip),%rsi        # 62c1 <_IO_stdin_used+0x2c1>
    26cb:	31 c0                	xor    %eax,%eax
    26cd:	bf 01 00 00 00       	mov    $0x1,%edi
    26d2:	e8 59 fd ff ff       	call   2430 <__printf_chk@plt>
    26d7:	ba 0a 00 00 00       	mov    $0xa,%edx
    26dc:	48 8d 35 f8 3b 00 00 	lea    0x3bf8(%rip),%rsi        # 62db <_IO_stdin_used+0x2db>
    26e3:	31 c0                	xor    %eax,%eax
    26e5:	bf 01 00 00 00       	mov    $0x1,%edi
    26ea:	e8 41 fd ff ff       	call   2430 <__printf_chk@plt>
    26ef:	48 8d 3d d8 39 00 00 	lea    0x39d8(%rip),%rdi        # 60ce <_IO_stdin_used+0xce>
    26f6:	e8 d5 fb ff ff       	call   22d0 <puts@plt>
  struct ProtectedState *protected_state = calloc(1, sizeof(struct ProtectedState));
    26fb:	be 18 00 00 00       	mov    $0x18,%esi
    2700:	bf 01 00 00 00       	mov    $0x1,%edi
    2705:	e8 76 fc ff ff       	call   2380 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    270a:	be 98 00 00 00       	mov    $0x98,%esi
    270f:	bf 09 00 00 00       	mov    $0x9,%edi
  struct ProtectedState *protected_state = calloc(1, sizeof(struct ProtectedState));
    2714:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2719:	e8 62 fc ff ff       	call   2380 <calloc@plt>
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    271e:	be 10 00 00 00       	mov    $0x10,%esi
    2723:	bf 01 00 00 00       	mov    $0x1,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2728:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    272d:	e8 4e fc ff ff       	call   2380 <calloc@plt>
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2732:	be 10 00 00 00       	mov    $0x10,%esi
    2737:	bf 01 00 00 00       	mov    $0x1,%edi
    buffers[x].count = buffer_size;
    273c:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
    2742:	48 89 c3             	mov    %rax,%rbx
    2745:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    274a:	e8 31 fc ff ff       	call   2380 <calloc@plt>
      buffers[x].buffer[y].available = 0;
    274f:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    }
  }
  int external_thread_index = 0;
    2754:	c7 44 24 34 00 00 00 00 	movl   $0x0,0x34(%rsp)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    275c:	48 89 43 08          	mov    %rax,0x8(%rbx)
      buffers[x].buffer[y].available = 0;
    2760:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    2767:	4d 89 c7             	mov    %r8,%r15
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
    276a:	4c 89 44 24 48       	mov    %r8,0x48(%rsp)
    276f:	90                   	nop
    thread_data[x].threads = thread_data;
    2770:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    thread_data[x].thread_index = x;
    2775:	45 89 37             	mov    %r14d,(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2778:	be 10 00 00 00       	mov    $0x10,%esi
      for (int y = 0 ; y < total_barrier_count ; y++) {
    277d:	31 db                	xor    %ebx,%ebx
    thread_data[x].task_count = total_barrier_count;
    277f:	41 c7 47 28 07 00 00 00 	movl   $0x7,0x28(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2787:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].threads = thread_data;
    278c:	49 89 47 10          	mov    %rax,0x10(%r15)
    thread_data[x].thread_count = thread_count;
    2790:	48 8b 05 59 42 00 00 	mov    0x4259(%rip),%rax        # 69f0 <_IO_stdin_used+0x9f0>
    2797:	44 89 74 24 08       	mov    %r14d,0x8(%rsp)
    279c:	49 89 47 18          	mov    %rax,0x18(%r15)
    thread_data[x].protected_state = protected_state;
    27a0:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    27a5:	49 89 47 30          	mov    %rax,0x30(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    27a9:	e8 d2 fb ff ff       	call   2380 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    27ae:	be 10 00 00 00       	mov    $0x10,%esi
    27b3:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    27b8:	49 89 47 50          	mov    %rax,0x50(%r15)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    27bc:	e8 bf fb ff ff       	call   2380 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    27c1:	be 28 00 00 00       	mov    $0x28,%esi
    27c6:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    27cb:	66 0f 6f 15 fd 41 00 00 	movdqa 0x41fd(%rip),%xmm2        # 69d0 <_IO_stdin_used+0x9d0>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    27d3:	49 89 47 58          	mov    %rax,0x58(%r15)
    thread_data[x].timestamp_count = 0;
    27d7:	41 0f 11 57 68       	movups %xmm2,0x68(%r15)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    27dc:	e8 9f fb ff ff       	call   2380 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    27e1:	be 00 02 00 00       	mov    $0x200,%esi
    27e6:	bf 07 00 00 00       	mov    $0x7,%edi
    thread_data[x].task_timestamp_count = 0;
    27eb:	66 0f 6f 1d dd 41 00 00 	movdqa 0x41dd(%rip),%xmm3        # 69d0 <_IO_stdin_used+0x9d0>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    27f3:	49 89 47 78          	mov    %rax,0x78(%r15)
    thread_data[x].task_timestamp_count = 0;
    27f7:	41 0f 11 9f 80 00 00 00 	movups %xmm3,0x80(%r15)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    27ff:	e8 7c fb ff ff       	call   2380 <calloc@plt>
        thread_data[x].tasks[y].sending = 1;
    2804:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
      thread_data[x].tasks = barriers;
    2809:	49 89 47 20          	mov    %rax,0x20(%r15)
        thread_data[x].tasks[y].sending = 1;
    280d:	49 89 c7             	mov    %rax,%r15
            thread_data[x].tasks[y].protected = do_protected_write; 
    2810:	4c 63 e3             	movslq %ebx,%r12
    2813:	44 89 74 24 28       	mov    %r14d,0x28(%rsp)
    2818:	4d 89 e5             	mov    %r12,%r13
    281b:	49 c1 e5 09          	shl    $0x9,%r13
        if (x == y) {
    281f:	44 39 f3             	cmp    %r14d,%ebx
    2822:	0f 84 c0 09 00 00    	je     31e8 <main+0xc18>
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    2828:	be 20 00 00 00       	mov    $0x20,%esi
    282d:	bf 06 00 00 00       	mov    $0x6,%edi
    2832:	e8 49 fb ff ff       	call   2380 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    2837:	89 5c 24 18          	mov    %ebx,0x18(%rsp)
    283b:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
    2840:	48 8d a8 c0 00 00 00 	lea    0xc0(%rax),%rbp
    2847:	4b 89 84 2f b0 01 00 00 	mov    %rax,0x1b0(%r15,%r13,1)
        for (int b = 0 ; b < thread_count ; b++) {
    284f:	49 89 c7             	mov    %rax,%r15
    2852:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2858:	be 08 00 00 00       	mov    $0x8,%esi
    285d:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < thread_count ; b++) {
    2862:	49 83 c7 20          	add    $0x20,%r15
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2866:	e8 15 fb ff ff       	call   2380 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    286b:	be 08 00 00 00       	mov    $0x8,%esi
    2870:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2875:	49 89 c4             	mov    %rax,%r12
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2878:	e8 03 fb ff ff       	call   2380 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    287d:	be 18 00 00 00       	mov    $0x18,%esi
    2882:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2887:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    288a:	e8 f1 fa ff ff       	call   2380 <calloc@plt>
          data[0].messages_count = 0;
    288f:	66 0f 6f 05 49 41 00 00 	movdqa 0x4149(%rip),%xmm0        # 69e0 <_IO_stdin_used+0x9e0>
          mailboxes[b].higher = &data[1];
    2897:	48 8d 70 18          	lea    0x18(%rax),%rsi
          mailboxes[b].lower = &data[0];
    289b:	49 89 47 e0          	mov    %rax,-0x20(%r15)
          mailboxes[b].higher = &data[1];
    289f:	49 89 77 e8          	mov    %rsi,-0x18(%r15)
          data[0].messages = messages;
    28a3:	4c 89 20             	mov    %r12,(%rax)
          data[1].messages = messages2;
    28a6:	48 89 58 18          	mov    %rbx,0x18(%rax)
          data[0].messages_count = 0;
    28aa:	0f 11 40 08          	movups %xmm0,0x8(%rax)
          data[1].messages_count = 0;
    28ae:	0f 11 40 20          	movups %xmm0,0x20(%rax)
        for (int b = 0 ; b < thread_count ; b++) {
    28b2:	49 39 ef             	cmp    %rbp,%r15
    28b5:	75 a1                	jne    2858 <main+0x288>
        char *message = malloc(sizeof(char) * 256);
    28b7:	be 01 00 00 00       	mov    $0x1,%esi
    28bc:	bf 00 01 00 00       	mov    $0x100,%edi
    28c1:	8b 5c 24 18          	mov    0x18(%rsp),%ebx
    28c5:	4c 8b 64 24 20       	mov    0x20(%rsp),%r12
    28ca:	e8 b1 fa ff ff       	call   2380 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    28cf:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    28d4:	48 89 c5             	mov    %rax,%rbp
        struct Message *messaged = malloc(sizeof(struct Message));
    28d7:	e8 14 fb ff ff       	call   23f0 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    28dc:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    28e1:	48 89 ef             	mov    %rbp,%rdi
    28e4:	41 89 d9             	mov    %ebx,%r9d
    28e7:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    28ec:	48 8d 0d 8d 3c 00 00 	lea    0x3c8d(%rip),%rcx        # 6580 <_IO_stdin_used+0x580>
    28f3:	ba 00 01 00 00       	mov    $0x100,%edx
    28f8:	31 c0                	xor    %eax,%eax
    28fa:	be 01 00 00 00       	mov    $0x1,%esi
    28ff:	e8 fc fb ff ff       	call   2500 <__sprintf_chk@plt>
        messaged->message = message;
    2904:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2909:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    290e:	ba ab aa aa aa       	mov    $0xaaaaaaab,%edx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2913:	be 20 00 00 00       	mov    $0x20,%esi
    2918:	bf 3f 42 0f 00       	mov    $0xf423f,%edi
        messaged->task_index = y;
    291d:	4d 89 62 10          	mov    %r12,0x10(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2921:	44 8d 63 01          	lea    0x1(%rbx),%r12d
    2925:	4c 8b 78 20          	mov    0x20(%rax),%r15
    2929:	44 89 e0             	mov    %r12d,%eax
    292c:	44 89 e1             	mov    %r12d,%ecx
        messaged->message = message;
    292f:	49 89 2a             	mov    %rbp,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2932:	48 0f af c2          	imul   %rdx,%rax
    2936:	4b 8d 2c 2f          	lea    (%r15,%r13,1),%rbp
        messaged->thread_index = x;
    293a:	4d 89 72 08          	mov    %r14,0x8(%r10)
        thread_data[x].tasks[y].message = messaged;
    293e:	4c 89 95 c8 01 00 00 	mov    %r10,0x1c8(%rbp)
        thread_data[x].tasks[y].snapshot_count = 999999;
    2945:	48 c7 85 98 01 00 00 3f 42 0f 00 	movq   $0xf423f,0x198(%rbp)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2950:	48 c1 e8 22          	shr    $0x22,%rax
    2954:	8d 04 40             	lea    (%rax,%rax,2),%eax
    2957:	01 c0                	add    %eax,%eax
    2959:	29 c1                	sub    %eax,%ecx
    295b:	89 8d d0 01 00 00    	mov    %ecx,0x1d0(%rbp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2961:	e8 1a fa ff ff       	call   2380 <calloc@plt>
        thread_data[x].tasks[y].thread_index = x;
    2966:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
        thread_data[x].tasks[y].task_index = y;
    296a:	89 5d 00             	mov    %ebx,0x0(%rbp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    296d:	48 89 85 90 01 00 00 	mov    %rax,0x190(%rbp)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2974:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2979:	48 c7 85 a0 01 00 00 00 00 00 00 	movq   $0x0,0x1a0(%rbp)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2984:	48 89 85 28 01 00 00 	mov    %rax,0x128(%rbp)
        thread_data[x].tasks[y].available = 1;
    298b:	48 8b 05 66 40 00 00 	mov    0x4066(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
        thread_data[x].tasks[y].thread_index = x;
    2992:	89 8d 30 01 00 00    	mov    %ecx,0x130(%rbp)
        thread_data[x].tasks[y].available = 1;
    2998:	48 89 85 80 01 00 00 	mov    %rax,0x180(%rbp)
        thread_data[x].tasks[y].sending = 1;
    299f:	48 b8 01 00 00 00 06 00 00 00 	movabs $0x600000001,%rax
        thread_data[x].tasks[y].arrived = 0;
    29a9:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        thread_data[x].tasks[y].thread_count = thread_count;
    29b3:	c7 85 34 01 00 00 06 00 00 00 	movl   $0x6,0x134(%rbp)
        thread_data[x].tasks[y].sending = 1;
    29bd:	48 89 85 c0 01 00 00 	mov    %rax,0x1c0(%rbp)
        if (y == barrier_count - 1) {
    29c4:	83 fb 05             	cmp    $0x5,%ebx
    29c7:	0f 84 fb 07 00 00    	je     31c8 <main+0xbf8>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    29cd:	8b 44 24 28          	mov    0x28(%rsp),%eax
    29d1:	39 c3                	cmp    %eax,%ebx
    29d3:	75 63                	jne    2a38 <main+0x468>
    29d5:	8b 5c 24 34          	mov    0x34(%rsp),%ebx
    29d9:	85 db                	test   %ebx,%ebx
    29db:	7f 5b                	jg     2a38 <main+0x468>
    29dd:	89 ca                	mov    %ecx,%edx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    29df:	bf 01 00 00 00       	mov    $0x1,%edi
    29e4:	48 8d 35 bd 3b 00 00 	lea    0x3bbd(%rip),%rsi        # 65a8 <_IO_stdin_used+0x5a8>
    29eb:	31 c0                	xor    %eax,%eax
    29ed:	e8 3e fa ff ff       	call   2430 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    29f2:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    29f7:	48 63 c3             	movslq %ebx,%rax
    29fa:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    29ff:	48 89 c1             	mov    %rax,%rcx
    2a02:	48 c1 e0 04          	shl    $0x4,%rax
    2a06:	48 01 f8             	add    %rdi,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2a09:	4c 8b 7a 20          	mov    0x20(%rdx),%r15
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a0d:	48 89 42 38          	mov    %rax,0x38(%rdx)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2a11:	48 8d 05 e8 2a 00 00 	lea    0x2ae8(%rip),%rax        # 5500 <barriered_work_ingest>
    2a18:	4b 89 84 2f 18 01 00 00 	mov    %rax,0x118(%r15,%r13,1)
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a20:	8d 41 01             	lea    0x1(%rcx),%eax
    2a23:	89 44 24 34          	mov    %eax,0x34(%rsp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2a27:	41 83 fc 07          	cmp    $0x7,%r12d
    2a2b:	74 1f                	je     2a4c <main+0x47c>
  int external_thread_index = 0;
    2a2d:	44 89 e3             	mov    %r12d,%ebx
    2a30:	e9 db fd ff ff       	jmp    2810 <main+0x240>
    2a35:	0f 1f 00             	nopl   (%rax)
            thread_data[x].tasks[y].run = barriered_work; 
    2a38:	48 8d 05 41 27 00 00 	lea    0x2741(%rip),%rax        # 5180 <barriered_work>
    2a3f:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2a46:	41 83 fc 07          	cmp    $0x7,%r12d
    2a4a:	75 e1                	jne    2a2d <main+0x45d>

          }
        }
      }
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2a4c:	4d 89 fc             	mov    %r15,%r12
    2a4f:	48 8d 05 ea 08 00 00 	lea    0x8ea(%rip),%rax        # 3340 <barriered_reset>
    2a56:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
  for (int x = 0 ; x < total_threads ; x++) {
    2a5b:	49 83 c6 01          	add    $0x1,%r14
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2a5f:	49 89 84 24 18 0d 00 00 	mov    %rax,0xd18(%r12)
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = thread_count; 
      thread_data[x].tasks[barrier_count].thread_index = x; 
    2a67:	8b 44 24 08          	mov    0x8(%rsp),%eax
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2a6b:	4d 89 bc 24 28 0d 00 00 	mov    %r15,0xd28(%r12)
  for (int x = 0 ; x < total_threads ; x++) {
    2a73:	49 81 c7 98 00 00 00 	add    $0x98,%r15
      thread_data[x].tasks[barrier_count].thread_index = x; 
    2a7a:	41 89 84 24 30 0d 00 00 	mov    %eax,0xd30(%r12)
      thread_data[x].tasks[barrier_count].available = 1; 
    2a82:	48 8b 05 6f 3f 00 00 	mov    0x3f6f(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2a89:	41 c7 84 24 80 0c 00 00 00 00 00 00 	movl   $0x0,0xc80(%r12)
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2a95:	41 c7 84 24 00 0c 00 00 06 00 00 00 	movl   $0x6,0xc00(%r12)
      thread_data[x].tasks[barrier_count].thread_count = thread_count; 
    2aa1:	41 c7 84 24 34 0d 00 00 06 00 00 00 	movl   $0x6,0xd34(%r12)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2aad:	41 c7 84 24 c4 0d 00 00 06 00 00 00 	movl   $0x6,0xdc4(%r12)
      thread_data[x].tasks[barrier_count].available = 1; 
    2ab9:	49 89 84 24 80 0d 00 00 	mov    %rax,0xd80(%r12)
  for (int x = 0 ; x < total_threads ; x++) {
    2ac1:	49 83 fe 09          	cmp    $0x9,%r14
    2ac5:	0f 85 a5 fc ff ff    	jne    2770 <main+0x1a0>
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].threads = thread_data;
    2acb:	4c 8b 44 24 48       	mov    0x48(%rsp),%r8
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ad0:	be 38 00 00 00       	mov    $0x38,%esi
    2ad5:	bf 09 00 00 00       	mov    $0x9,%edi
  thread_data[thread_count].thread_count = thread_count;
  thread_data[thread_count].thread_index = 0;

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
  for (int x = 0 ; x < thread_count ; x++) {
    2ada:	45 31 ed             	xor    %r13d,%r13d
    2add:	4c 8d 3d cc 08 00 00 	lea    0x8cc(%rip),%r15        # 33b0 <barriered_thread>
    thread_data[n].tasks[0].scheduled = 1;
    2ae4:	49 8b 40 20          	mov    0x20(%r8),%rax
    2ae8:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    thread_data[x].threads = thread_data;
    2aed:	4d 89 80 38 04 00 00 	mov    %r8,0x438(%r8)
    thread_data[x].thread_count = thread_count;
    2af4:	41 c7 80 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r8)
    thread_data[x].thread_index = x;
    2aff:	41 c7 80 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r8)
    thread_data[x].task_count = total_barrier_count;
    2b0a:	41 c7 80 50 04 00 00 07 00 00 00 	movl   $0x7,0x450(%r8)
    thread_data[n].tasks[0].scheduled = 1;
    2b15:	c7 80 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rax)
    2b1f:	49 8b 80 b8 00 00 00 	mov    0xb8(%r8),%rax
    2b26:	c7 80 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rax)
    2b30:	49 8b 80 50 01 00 00 	mov    0x150(%r8),%rax
    2b37:	c7 80 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rax)
    2b41:	49 8b 80 e8 01 00 00 	mov    0x1e8(%r8),%rax
    2b48:	c7 80 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rax)
    2b52:	49 8b 80 80 02 00 00 	mov    0x280(%r8),%rax
    2b59:	c7 80 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rax)
    2b63:	49 8b 80 18 03 00 00 	mov    0x318(%r8),%rax
    2b6a:	c7 80 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rax)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b74:	e8 07 f8 ff ff       	call   2380 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b79:	be 38 00 00 00       	mov    $0x38,%esi
    2b7e:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b83:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b86:	e8 f5 f7 ff ff       	call   2380 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b8b:	be 38 00 00 00       	mov    $0x38,%esi
    2b90:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b95:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b9a:	e8 e1 f7 ff ff       	call   2380 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2b9f:	be 08 00 00 00       	mov    $0x8,%esi
    2ba4:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ba9:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2bae:	e8 cd f7 ff ff       	call   2380 <calloc@plt>
  thread_data[thread_count].task_count = total_barrier_count;
    2bb3:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2bb8:	ba 06 00 00 00       	mov    $0x6,%edx
    2bbd:	48 8d 35 2b 37 00 00 	lea    0x372b(%rip),%rsi        # 62ef <_IO_stdin_used+0x2ef>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2bc4:	49 89 c4             	mov    %rax,%r12
  thread_data[thread_count].task_count = total_barrier_count;
    2bc7:	48 8b 05 32 3e 00 00 	mov    0x3e32(%rip),%rax        # 6a00 <_IO_stdin_used+0xa00>
    2bce:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].threads = thread_data;
    2bd3:	4d 89 80 a0 03 00 00 	mov    %r8,0x3a0(%r8)
    2bda:	4c 89 e5             	mov    %r12,%rbp
  thread_data[thread_count].task_count = total_barrier_count;
    2bdd:	49 89 80 b8 03 00 00 	mov    %rax,0x3b8(%r8)
    2be4:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2be6:	41 c7 80 a8 03 00 00 06 00 00 00 	movl   $0x6,0x3a8(%r8)
  thread_data[thread_count].thread_index = 0;
    2bf1:	49 c7 80 90 03 00 00 00 00 00 00 	movq   $0x0,0x390(%r8)
    2bfc:	e8 2f f8 ff ff       	call   2430 <__printf_chk@plt>
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2c01:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2c06:	49 8d 7c 24 30       	lea    0x30(%r12),%rdi
    2c0b:	45 89 ec             	mov    %r13d,%r12d
    2c0e:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
    2c15:	48 8d 15 04 0b 00 00 	lea    0xb04(%rip),%rdx        # 3720 <timer_thread>
    2c1c:	49 89 ed             	mov    %rbp,%r13
    2c1f:	49 8d 88 90 03 00 00 	lea    0x390(%r8),%rcx
    2c26:	e8 25 f8 ff ff       	call   2450 <pthread_create@plt>
    2c2b:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    thread_data[x].type = WORKER;
    2c30:	41 c7 46 04 01 00 00 00 	movl   $0x1,0x4(%r14)
    2c38:	44 89 e2             	mov    %r12d,%edx
    2c3b:	bf 01 00 00 00       	mov    $0x1,%edi
    2c40:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2c42:	41 c7 46 2c 01 00 00 00 	movl   $0x1,0x2c(%r14)
    2c4a:	48 8d 35 77 39 00 00 	lea    0x3977(%rip),%rsi        # 65c8 <_IO_stdin_used+0x5c8>
  for (int x = 0 ; x < thread_count ; x++) {
    2c51:	41 83 c4 01          	add    $0x1,%r12d
    2c55:	e8 d6 f7 ff ff       	call   2430 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &timer_attr[x], &barriered_thread, &thread_data[x]);
    2c5a:	4c 89 f1             	mov    %r14,%rcx
    2c5d:	48 89 de             	mov    %rbx,%rsi
    2c60:	48 89 ef             	mov    %rbp,%rdi
    2c63:	4c 89 fa             	mov    %r15,%rdx
  for (int x = 0 ; x < thread_count ; x++) {
    2c66:	49 81 c6 98 00 00 00 	add    $0x98,%r14
    2c6d:	48 83 c5 08          	add    $0x8,%rbp
    2c71:	48 83 c3 38          	add    $0x38,%rbx
    pthread_create(&thread[x], &timer_attr[x], &barriered_thread, &thread_data[x]);
    2c75:	e8 d6 f7 ff ff       	call   2450 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2c7a:	41 83 fc 06          	cmp    $0x6,%r12d
    2c7e:	75 b0                	jne    2c30 <main+0x660>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    2c80:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    2c85:	48 8b 1d 7c 3d 00 00 	mov    0x3d7c(%rip),%rbx        # 6a08 <_IO_stdin_used+0xa08>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2c8c:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    2c91:	4d 89 ec             	mov    %r13,%r12
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2c94:	bf 01 00 00 00       	mov    $0x1,%edi
    2c99:	48 8d 2d bf 36 00 00 	lea    0x36bf(%rip),%rbp        # 635f <_IO_stdin_used+0x35f>
    thread_data[x].task_count = 0;
    2ca0:	49 89 98 50 04 00 00 	mov    %rbx,0x450(%r8)
    thread_data[x].type = IO;
    2ca7:	41 c7 80 2c 04 00 00 02 00 00 00 	movl   $0x2,0x42c(%r8)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2cb2:	e8 c9 f6 ff ff       	call   2380 <calloc@plt>
    2cb7:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2cbc:	be 00 08 00 00       	mov    $0x800,%esi
    2cc1:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2cc3:	49 89 80 68 04 00 00 	mov    %rax,0x468(%r8)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2cca:	e8 c1 f7 ff ff       	call   2490 <eventfd@plt>
    2ccf:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2cd4:	ba 07 00 00 00       	mov    $0x7,%edx
    2cd9:	48 8d 35 2d 36 00 00 	lea    0x362d(%rip),%rsi        # 630d <_IO_stdin_used+0x30d>
    2ce0:	bf 01 00 00 00       	mov    $0x1,%edi
    2ce5:	41 89 80 70 04 00 00 	mov    %eax,0x470(%r8)
    2cec:	31 c0                	xor    %eax,%eax
    thread_data[x].threads = thread_data;
    2cee:	4d 89 80 38 04 00 00 	mov    %r8,0x438(%r8)
    thread_data[x].thread_count = thread_count;
    2cf5:	41 c7 80 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r8)
    thread_data[x].thread_index = x;
    2d00:	41 c7 80 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r8)
    2d0b:	e8 20 f7 ff ff       	call   2430 <__printf_chk@plt>
    thread_data[x].type = IO;
    2d10:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2d15:	49 8d 7d 38          	lea    0x38(%r13),%rdi
    2d19:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    2d1e:	48 8d 15 7b 1c 00 00 	lea    0x1c7b(%rip),%rdx        # 49a0 <io_thread>
    thread_data[x].type = IO;
    2d25:	49 8d 88 28 04 00 00 	lea    0x428(%r8),%rcx
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2d2c:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    2d33:	e8 18 f7 ff ff       	call   2450 <pthread_create@plt>
    2d38:	ba 08 00 00 00       	mov    $0x8,%edx
    2d3d:	48 8d 35 e0 35 00 00 	lea    0x35e0(%rip),%rsi        # 6324 <_IO_stdin_used+0x324>
    2d44:	31 c0                	xor    %eax,%eax
    2d46:	bf 01 00 00 00       	mov    $0x1,%edi
    2d4b:	e8 e0 f6 ff ff       	call   2430 <__printf_chk@plt>
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    2d50:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    thread_data[x].buffers = &buffers[buffer_index];
    2d55:	48 8b 44 24 38       	mov    0x38(%rsp),%rax

    thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2d5a:	49 8d 7d 40          	lea    0x40(%r13),%rdi
    2d5e:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    2d63:	48 8d 15 f6 08 00 00 	lea    0x8f6(%rip),%rdx        # 3660 <external_thread>
    2d6a:	4c 8d 6c 24 50       	lea    0x50(%rsp),%r13
    thread_data[x].buffers = &buffers[buffer_index];
    2d6f:	49 89 80 f8 04 00 00 	mov    %rax,0x4f8(%r8)
    thread_data[x].thread_count = thread_count;
    2d76:	48 8b 05 73 3c 00 00 	mov    0x3c73(%rip),%rax        # 69f0 <_IO_stdin_used+0x9f0>
    thread_data[x].type = EXTERNAL;
    2d7d:	49 8d 88 c0 04 00 00 	lea    0x4c0(%r8),%rcx
    thread_data[x].task_count = 0;
    2d84:	49 89 98 e8 04 00 00 	mov    %rbx,0x4e8(%r8)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2d8b:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
    2d92:	31 db                	xor    %ebx,%ebx
    thread_data[x].thread_count = thread_count;
    2d94:	49 89 80 d8 04 00 00 	mov    %rax,0x4d8(%r8)
    thread_data[x].thread_index = x;
    2d9b:	48 8b 05 6e 3c 00 00 	mov    0x3c6e(%rip),%rax        # 6a10 <_IO_stdin_used+0xa10>
    thread_data[x].threads = thread_data;
    2da2:	4d 89 80 d0 04 00 00 	mov    %r8,0x4d0(%r8)
    thread_data[x].thread_index = x;
    2da9:	49 89 80 c0 04 00 00 	mov    %rax,0x4c0(%r8)
    thread_data[x].type = EXTERNAL;
    2db0:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2db5:	e8 96 f6 ff ff       	call   2450 <pthread_create@plt>
    2dba:	48 8d 3d 80 35 00 00 	lea    0x3580(%rip),%rdi        # 6341 <_IO_stdin_used+0x341>
    2dc1:	e8 0a f5 ff ff       	call   22d0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    2dc6:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    2dcb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    void * result; 
    pthread_join(thread[x], &result);
    2dd0:	49 8b 3c dc          	mov    (%r12,%rbx,8),%rdi
    2dd4:	4c 89 ee             	mov    %r13,%rsi
    2dd7:	e8 f4 f6 ff ff       	call   24d0 <pthread_join@plt>
    2ddc:	89 da                	mov    %ebx,%edx
    2dde:	48 89 ee             	mov    %rbp,%rsi
    2de1:	bf 01 00 00 00       	mov    $0x1,%edi
    2de6:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    2de8:	48 83 c3 01          	add    $0x1,%rbx
    2dec:	e8 3f f6 ff ff       	call   2430 <__printf_chk@plt>
    2df1:	48 83 fb 09          	cmp    $0x9,%rbx
    2df5:	75 d9                	jne    2dd0 <main+0x800>
    2df7:	49 8d 86 b0 03 00 00 	lea    0x3b0(%r14),%rax
  }
  long total = 0;
  long v = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
    2dfe:	31 ed                	xor    %ebp,%ebp
  long sends = 0;
    2e00:	31 c9                	xor    %ecx,%ecx
  long v = 0;
    2e02:	45 31 c9             	xor    %r9d,%r9d
  long total = 0;
    2e05:	45 31 e4             	xor    %r12d,%r12d
    2e08:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  long ingests = 0;
    2e0d:	45 31 db             	xor    %r11d,%r11d
    2e10:	4d 8d 6e 20          	lea    0x20(%r14),%r13
    2e14:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
  long received = 0;
    2e19:	31 db                	xor    %ebx,%ebx
    2e1b:	4d 89 de             	mov    %r11,%r14
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
      struct timespec start = thread_data[x].start[n];
      struct timespec end = thread_data[x].end[n];
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    2e1e:	49 bf db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r15
    2e28:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2e2d:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    2e32:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    2e37:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2e40:	49 63 45 08          	movslq 0x8(%r13),%rax
    2e44:	85 c0                	test   %eax,%eax
    2e46:	0f 8e 9d 00 00 00    	jle    2ee9 <main+0x919>
    2e4c:	49 8b 55 00          	mov    0x0(%r13),%rdx
    2e50:	48 c1 e0 09          	shl    $0x9,%rax
    2e54:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    2e59:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    2e5e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    2e63:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    2e68:	48 8d 34 10          	lea    (%rax,%rdx,1),%rsi
    2e6c:	0f 1f 40 00          	nopl   0x0(%rax)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2e70:	48 8b 82 b0 01 00 00 	mov    0x1b0(%rdx),%rax
      total += thread_data[x].tasks[n].n;
    2e77:	48 03 8a 08 01 00 00 	add    0x108(%rdx),%rcx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2e7e:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
      v += thread_data[x].tasks[n].v;
    2e85:	4c 03 9a 10 ff ff ff 	add    -0xf0(%rdx),%r11
      ingests += thread_data[x].tasks[n].ingest_count;
    2e8c:	4c 03 72 a8          	add    -0x58(%rdx),%r14
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2e90:	48 03 68 10          	add    0x10(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2e94:	48 03 58 18          	add    0x18(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2e98:	48 03 68 30          	add    0x30(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2e9c:	48 03 58 38          	add    0x38(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ea0:	48 03 68 50          	add    0x50(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2ea4:	48 03 58 58          	add    0x58(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ea8:	48 03 68 70          	add    0x70(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2eac:	48 03 58 78          	add    0x78(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2eb0:	48 03 a8 90 00 00 00 	add    0x90(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2eb7:	48 03 98 98 00 00 00 	add    0x98(%rax),%rbx
      sends += thread_data[x].tasks[n].sends;
    2ebe:	4c 03 4a b8          	add    -0x48(%rdx),%r9
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ec2:	48 03 a8 b0 00 00 00 	add    0xb0(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2ec9:	48 03 98 b8 00 00 00 	add    0xb8(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2ed0:	48 39 f2             	cmp    %rsi,%rdx
    2ed3:	75 9b                	jne    2e70 <main+0x8a0>
    2ed5:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    2eda:	4c 89 5c 24 10       	mov    %r11,0x10(%rsp)
    2edf:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    2ee4:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2ee9:	45 31 e4             	xor    %r12d,%r12d
    2eec:	49 83 7d 50 00       	cmpq   $0x0,0x50(%r13)
    2ef1:	7e 74                	jle    2f67 <main+0x997>
    2ef3:	4c 89 ed             	mov    %r13,%rbp
    2ef6:	49 89 dd             	mov    %rbx,%r13
    2ef9:	4c 89 e3             	mov    %r12,%rbx
    2efc:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec start = thread_data[x].start[n];
    2f00:	48 8b 7d 30          	mov    0x30(%rbp),%rdi
    2f04:	48 89 de             	mov    %rbx,%rsi
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2f07:	48 83 c3 01          	add    $0x1,%rbx
    2f0b:	48 c1 e6 04          	shl    $0x4,%rsi
      struct timespec start = thread_data[x].start[n];
    2f0f:	48 01 f7             	add    %rsi,%rdi
      struct timespec end = thread_data[x].end[n];
    2f12:	48 03 75 38          	add    0x38(%rbp),%rsi
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    2f16:	48 8b 56 08          	mov    0x8(%rsi),%rdx
    2f1a:	48 2b 57 08          	sub    0x8(%rdi),%rdx
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    2f1e:	48 89 d0             	mov    %rdx,%rax
    2f21:	49 f7 e7             	mul    %r15
    2f24:	31 c0                	xor    %eax,%eax
    2f26:	48 89 d1             	mov    %rdx,%rcx
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    2f29:	48 8b 16             	mov    (%rsi),%rdx
    2f2c:	48 8d 35 40 34 00 00 	lea    0x3440(%rip),%rsi        # 6373 <_IO_stdin_used+0x373>
    2f33:	48 2b 17             	sub    (%rdi),%rdx
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    2f36:	48 c1 e9 12          	shr    $0x12,%rcx
    2f3a:	bf 01 00 00 00       	mov    $0x1,%edi
    2f3f:	e8 ec f4 ff ff       	call   2430 <__printf_chk@plt>
    2f44:	48 8b 55 40          	mov    0x40(%rbp),%rdx
    2f48:	bf 01 00 00 00       	mov    $0x1,%edi
    2f4d:	31 c0                	xor    %eax,%eax
    2f4f:	48 8d 35 3b 34 00 00 	lea    0x343b(%rip),%rsi        # 6391 <_IO_stdin_used+0x391>
    2f56:	e8 d5 f4 ff ff       	call   2430 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2f5b:	48 39 5d 50          	cmp    %rbx,0x50(%rbp)
    2f5f:	7f 9f                	jg     2f00 <main+0x930>
    2f61:	4c 89 eb             	mov    %r13,%rbx
    2f64:	49 89 ed             	mov    %rbp,%r13
      printf("%ld iterations\n", thread_data[x].iteration_count);
    }
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    2f67:	45 31 e4             	xor    %r12d,%r12d
    2f6a:	49 83 7d 68 00       	cmpq   $0x0,0x68(%r13)
    2f6f:	0f 8e 8a 00 00 00    	jle    2fff <main+0xa2f>
    2f75:	4c 89 ed             	mov    %r13,%rbp
    2f78:	49 89 dd             	mov    %rbx,%r13
    2f7b:	4c 89 e3             	mov    %r12,%rbx
    2f7e:	66 90                	xchg   %ax,%ax
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    2f80:	48 8b 45 58          	mov    0x58(%rbp),%rax
    2f84:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    2f88:	48 83 ec 08          	sub    $0x8,%rsp
    2f8c:	48 8d 35 5d 36 00 00 	lea    0x365d(%rip),%rsi        # 65f0 <_IO_stdin_used+0x5f0>
    2f93:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    2f98:	48 83 c3 01          	add    $0x1,%rbx
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    2f9c:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    2fa0:	4c 8b 61 18          	mov    0x18(%rcx),%r12
    2fa4:	4c 2b 61 08          	sub    0x8(%rcx),%r12
      printf("all %d task %d synchronized in %lds %ldms %ld ns \n", thread_count, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    2fa8:	4c 89 e0             	mov    %r12,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    2fab:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    2faf:	4c 2b 01             	sub    (%rcx),%r8
      printf("all %d task %d synchronized in %lds %ldms %ld ns \n", thread_count, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    2fb2:	49 f7 e7             	mul    %r15
    2fb5:	8b 49 20             	mov    0x20(%rcx),%ecx
    2fb8:	41 54                	push   %r12
    2fba:	31 c0                	xor    %eax,%eax
    2fbc:	48 c1 ea 12          	shr    $0x12,%rdx
    2fc0:	49 89 d1             	mov    %rdx,%r9
    2fc3:	ba 06 00 00 00       	mov    $0x6,%edx
    2fc8:	e8 63 f4 ff ff       	call   2430 <__printf_chk@plt>
    2fcd:	48 8d 35 d9 33 00 00 	lea    0x33d9(%rip),%rsi        # 63ad <_IO_stdin_used+0x3ad>
    2fd4:	bf 01 00 00 00       	mov    $0x1,%edi
      printf("%ldns per thread\n", (seconds2 / thread_count));
    2fd9:	48 b8 ab aa aa aa aa aa aa aa 	movabs $0xaaaaaaaaaaaaaaab,%rax
    2fe3:	49 f7 e4             	mul    %r12
    2fe6:	31 c0                	xor    %eax,%eax
    2fe8:	48 c1 ea 02          	shr    $0x2,%rdx
    2fec:	e8 3f f4 ff ff       	call   2430 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    2ff1:	58                   	pop    %rax
    2ff2:	5a                   	pop    %rdx
    2ff3:	48 39 5d 68          	cmp    %rbx,0x68(%rbp)
    2ff7:	7f 87                	jg     2f80 <main+0x9b0>
    2ff9:	4c 89 eb             	mov    %r13,%rbx
    2ffc:	49 89 ed             	mov    %rbp,%r13
    2fff:	49 8b 55 70          	mov    0x70(%r13),%rdx
    3003:	48 8d 35 97 33 00 00 	lea    0x3397(%rip),%rsi        # 63a1 <_IO_stdin_used+0x3a1>
    300a:	bf 01 00 00 00       	mov    $0x1,%edi
    300f:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < thread_count ; x++) {
    3011:	49 81 c5 98 00 00 00 	add    $0x98,%r13
    3018:	e8 13 f4 ff ff       	call   2430 <__printf_chk@plt>
    301d:	4c 39 6c 24 28       	cmp    %r13,0x28(%rsp)
    3022:	0f 85 18 fe ff ff    	jne    2e40 <main+0x870>
    3028:	4c 8b 64 24 08       	mov    0x8(%rsp),%r12
    302d:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    3032:	48 8d 35 86 33 00 00 	lea    0x3386(%rip),%rsi        # 63bf <_IO_stdin_used+0x3bf>
    3039:	31 c0                	xor    %eax,%eax
    303b:	bf 01 00 00 00       	mov    $0x1,%edi
    3040:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    3045:	4c 89 74 24 10       	mov    %r14,0x10(%rsp)
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total Protected %ld\n", protected_state->protected);
  printf("Total V %ld\n", v);
  printf("\n");
  printf("Total Protected per second %ld\n", protected_state->protected / DURATION);
    304a:	49 bd 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%r13
    3054:	4c 89 e2             	mov    %r12,%rdx
    3057:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    305c:	e8 cf f3 ff ff       	call   2430 <__printf_chk@plt>
    3061:	bf 0a 00 00 00       	mov    $0xa,%edi
    3066:	e8 55 f2 ff ff       	call   22c0 <putchar@plt>
    306b:	4c 8b 74 24 40       	mov    0x40(%rsp),%r14
    3070:	48 8d 35 5c 33 00 00 	lea    0x335c(%rip),%rsi        # 63d3 <_IO_stdin_used+0x3d3>
    3077:	31 c0                	xor    %eax,%eax
    3079:	bf 01 00 00 00       	mov    $0x1,%edi
    307e:	49 8b 16             	mov    (%r14),%rdx
    3081:	e8 aa f3 ff ff       	call   2430 <__printf_chk@plt>
    3086:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    308b:	48 8d 35 56 33 00 00 	lea    0x3356(%rip),%rsi        # 63e8 <_IO_stdin_used+0x3e8>
    3092:	31 c0                	xor    %eax,%eax
    3094:	bf 01 00 00 00       	mov    $0x1,%edi
    3099:	e8 92 f3 ff ff       	call   2430 <__printf_chk@plt>
    309e:	bf 0a 00 00 00       	mov    $0xa,%edi
    30a3:	e8 18 f2 ff ff       	call   22c0 <putchar@plt>
    30a8:	49 8b 36             	mov    (%r14),%rsi
    30ab:	bf 01 00 00 00       	mov    $0x1,%edi
    30b0:	48 89 f0             	mov    %rsi,%rax
    30b3:	48 c1 fe 3f          	sar    $0x3f,%rsi
    30b7:	49 f7 ed             	imul   %r13
    30ba:	31 c0                	xor    %eax,%eax
    30bc:	48 c1 fa 02          	sar    $0x2,%rdx
    30c0:	48 29 f2             	sub    %rsi,%rdx
    30c3:	48 8d 35 5e 35 00 00 	lea    0x355e(%rip),%rsi        # 6628 <_IO_stdin_used+0x628>
    30ca:	e8 61 f3 ff ff       	call   2430 <__printf_chk@plt>
    30cf:	49 8b 56 08          	mov    0x8(%r14),%rdx
    30d3:	bf 01 00 00 00       	mov    $0x1,%edi
    30d8:	31 c0                	xor    %eax,%eax
    30da:	48 8d 35 67 35 00 00 	lea    0x3567(%rip),%rsi        # 6648 <_IO_stdin_used+0x648>
    30e1:	e8 4a f3 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    30e6:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    30eb:	bf 01 00 00 00       	mov    $0x1,%edi
    30f0:	48 8d 35 79 35 00 00 	lea    0x3579(%rip),%rsi        # 6670 <_IO_stdin_used+0x670>
    30f7:	4c 89 d8             	mov    %r11,%rax
    30fa:	49 c1 fb 3f          	sar    $0x3f,%r11
    30fe:	49 f7 ed             	imul   %r13
    3101:	31 c0                	xor    %eax,%eax
    3103:	48 c1 fa 02          	sar    $0x2,%rdx
    3107:	4c 29 da             	sub    %r11,%rdx
    310a:	e8 21 f3 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    310f:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    3114:	bf 01 00 00 00       	mov    $0x1,%edi
    3119:	48 8d 35 80 35 00 00 	lea    0x3580(%rip),%rsi        # 66a0 <_IO_stdin_used+0x6a0>
    3120:	48 89 c8             	mov    %rcx,%rax
    3123:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3127:	49 f7 ed             	imul   %r13
    312a:	31 c0                	xor    %eax,%eax
    312c:	48 c1 fa 02          	sar    $0x2,%rdx
    3130:	48 29 ca             	sub    %rcx,%rdx
    3133:	e8 f8 f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3138:	4c 89 e0             	mov    %r12,%rax
    313b:	49 c1 fc 3f          	sar    $0x3f,%r12
    313f:	48 8d 35 8a 35 00 00 	lea    0x358a(%rip),%rsi        # 66d0 <_IO_stdin_used+0x6d0>
    3146:	49 f7 ed             	imul   %r13
    3149:	bf 01 00 00 00       	mov    $0x1,%edi
    314e:	48 c1 fa 02          	sar    $0x2,%rdx
    3152:	4c 29 e2             	sub    %r12,%rdx
    3155:	31 c0                	xor    %eax,%eax
    3157:	e8 d4 f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    315c:	48 89 e8             	mov    %rbp,%rax
    315f:	48 c1 fd 3f          	sar    $0x3f,%rbp
    3163:	48 8d 35 8b 32 00 00 	lea    0x328b(%rip),%rsi        # 63f5 <_IO_stdin_used+0x3f5>
    316a:	49 f7 ed             	imul   %r13
    316d:	bf 01 00 00 00       	mov    $0x1,%edi
    3172:	31 c0                	xor    %eax,%eax
    3174:	48 c1 fa 02          	sar    $0x2,%rdx
    3178:	48 29 ea             	sub    %rbp,%rdx
    317b:	e8 b0 f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    3180:	48 89 d8             	mov    %rbx,%rax
    3183:	48 c1 fb 3f          	sar    $0x3f,%rbx
    3187:	48 8d 35 78 32 00 00 	lea    0x3278(%rip),%rsi        # 6406 <_IO_stdin_used+0x406>
    318e:	49 f7 ed             	imul   %r13
    3191:	bf 01 00 00 00       	mov    $0x1,%edi
    3196:	31 c0                	xor    %eax,%eax
    3198:	48 c1 fa 02          	sar    $0x2,%rdx
    319c:	48 29 da             	sub    %rbx,%rdx
    319f:	e8 8c f2 ff ff       	call   2430 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    31a4:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    31a9:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    31b2:	75 48                	jne    31fc <main+0xc2c>
    31b4:	48 83 c4 68          	add    $0x68,%rsp
    31b8:	31 c0                	xor    %eax,%eax
    31ba:	5b                   	pop    %rbx
    31bb:	5d                   	pop    %rbp
    31bc:	41 5c                	pop    %r12
    31be:	41 5d                	pop    %r13
    31c0:	41 5e                	pop    %r14
    31c2:	41 5f                	pop    %r15
    31c4:	c3                   	ret
    31c5:	0f 1f 00             	nopl   (%rax)
          thread_data[x].tasks[y].run = barriered_work; 
    31c8:	48 8d 05 b1 1f 00 00 	lea    0x1fb1(%rip),%rax        # 5180 <barriered_work>
    31cf:	41 bc 06 00 00 00    	mov    $0x6,%r12d
    31d5:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    31dc:	e9 4c f8 ff ff       	jmp    2a2d <main+0x45d>
    31e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            thread_data[x].tasks[y].protected = do_protected_write; 
    31e8:	48 8d 05 11 01 00 00 	lea    0x111(%rip),%rax        # 3300 <do_protected_write>
    31ef:	4b 89 84 2f 20 01 00 00 	mov    %rax,0x120(%r15,%r13,1)
    31f7:	e9 2c f6 ff ff       	jmp    2828 <main+0x258>
}
    31fc:	e8 0f f1 ff ff       	call   2310 <__stack_chk_fail@plt>
    3201:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    320b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003210 <_start>:
    3210:	f3 0f 1e fa          	endbr64
    3214:	31 ed                	xor    %ebp,%ebp
    3216:	49 89 d1             	mov    %rdx,%r9
    3219:	5e                   	pop    %rsi
    321a:	48 89 e2             	mov    %rsp,%rdx
    321d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3221:	50                   	push   %rax
    3222:	54                   	push   %rsp
    3223:	45 31 c0             	xor    %r8d,%r8d
    3226:	31 c9                	xor    %ecx,%ecx
    3228:	48 8d 3d a1 f3 ff ff 	lea    -0xc5f(%rip),%rdi        # 25d0 <main>
    322f:	ff 15 a3 5d 00 00    	call   *0x5da3(%rip)        # 8fd8 <__libc_start_main@GLIBC_2.34>
    3235:	f4                   	hlt
    3236:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003240 <deregister_tm_clones>:
    3240:	48 8d 3d d9 5d 00 00 	lea    0x5dd9(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    3247:	48 8d 05 d2 5d 00 00 	lea    0x5dd2(%rip),%rax        # 9020 <stderr@GLIBC_2.2.5>
    324e:	48 39 f8             	cmp    %rdi,%rax
    3251:	74 15                	je     3268 <deregister_tm_clones+0x28>
    3253:	48 8b 05 86 5d 00 00 	mov    0x5d86(%rip),%rax        # 8fe0 <_ITM_deregisterTMCloneTable@Base>
    325a:	48 85 c0             	test   %rax,%rax
    325d:	74 09                	je     3268 <deregister_tm_clones+0x28>
    325f:	ff e0                	jmp    *%rax
    3261:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3268:	c3                   	ret
    3269:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003270 <register_tm_clones>:
    3270:	48 8d 3d a9 5d 00 00 	lea    0x5da9(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    3277:	48 8d 35 a2 5d 00 00 	lea    0x5da2(%rip),%rsi        # 9020 <stderr@GLIBC_2.2.5>
    327e:	48 29 fe             	sub    %rdi,%rsi
    3281:	48 89 f0             	mov    %rsi,%rax
    3284:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3288:	48 c1 f8 03          	sar    $0x3,%rax
    328c:	48 01 c6             	add    %rax,%rsi
    328f:	48 d1 fe             	sar    %rsi
    3292:	74 14                	je     32a8 <register_tm_clones+0x38>
    3294:	48 8b 05 55 5d 00 00 	mov    0x5d55(%rip),%rax        # 8ff0 <_ITM_registerTMCloneTable@Base>
    329b:	48 85 c0             	test   %rax,%rax
    329e:	74 08                	je     32a8 <register_tm_clones+0x38>
    32a0:	ff e0                	jmp    *%rax
    32a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    32a8:	c3                   	ret
    32a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000032b0 <__do_global_dtors_aux>:
    32b0:	f3 0f 1e fa          	endbr64
    32b4:	80 3d 6d 5d 00 00 00 	cmpb   $0x0,0x5d6d(%rip)        # 9028 <completed.0>
    32bb:	75 2b                	jne    32e8 <__do_global_dtors_aux+0x38>
    32bd:	55                   	push   %rbp
    32be:	48 83 3d 32 5d 00 00 00 	cmpq   $0x0,0x5d32(%rip)        # 8ff8 <__cxa_finalize@GLIBC_2.2.5>
    32c6:	48 89 e5             	mov    %rsp,%rbp
    32c9:	74 0c                	je     32d7 <__do_global_dtors_aux+0x27>
    32cb:	48 8b 3d 36 5d 00 00 	mov    0x5d36(%rip),%rdi        # 9008 <__dso_handle>
    32d2:	e8 c9 ef ff ff       	call   22a0 <__cxa_finalize@plt>
    32d7:	e8 64 ff ff ff       	call   3240 <deregister_tm_clones>
    32dc:	c6 05 45 5d 00 00 01 	movb   $0x1,0x5d45(%rip)        # 9028 <completed.0>
    32e3:	5d                   	pop    %rbp
    32e4:	c3                   	ret
    32e5:	0f 1f 00             	nopl   (%rax)
    32e8:	c3                   	ret
    32e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000032f0 <frame_dummy>:
    32f0:	f3 0f 1e fa          	endbr64
    32f4:	e9 77 ff ff ff       	jmp    3270 <register_tm_clones>
    32f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003300 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    3300:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3304:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    330b:	48 8b 40 30          	mov    0x30(%rax),%rax
  data->v++; // thread local
    330f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    3317:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    331b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    331f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3326:	48 85 c9             	test   %rcx,%rcx
    3329:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3330:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3334:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3338:	31 c0                	xor    %eax,%eax
    333a:	c3                   	ret
    333b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003340 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3340:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3344:	48 63 8f 84 01 00 00 	movslq 0x184(%rdi),%rcx
    334b:	85 c9                	test   %ecx,%ecx
    334d:	7e 57                	jle    33a6 <barriered_reset+0x66>
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    334f:	48 63 87 30 01 00 00 	movslq 0x130(%rdi),%rax
    3356:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    335d:	48 c1 e1 09          	shl    $0x9,%rcx
    3361:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3365:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    3369:	48 8b 56 10          	mov    0x10(%rsi),%rdx
      data->thread->tasks[x].available = 1; 
    336d:	48 8b 76 20          	mov    0x20(%rsi),%rsi
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    3371:	48 8d 04 c2          	lea    (%rdx,%rax,8),%rax
    3375:	48 8b 50 20          	mov    0x20(%rax),%rdx
      data->thread->tasks[x].available = 1; 
    3379:	31 c0                	xor    %eax,%eax
    337b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    3380:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index].tasks[x].prearrive++; 
    3388:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3390:	c7 84 06 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    339b:	48 05 00 02 00 00    	add    $0x200,%rax
    33a1:	48 39 c1             	cmp    %rax,%rcx
    33a4:	75 da                	jne    3380 <barriered_reset+0x40>
  asm volatile ("mfence" ::: "memory");
    33a6:	0f ae f0             	mfence
}
    33a9:	31 c0                	xor    %eax,%eax
    33ab:	c3                   	ret
    33ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000033b0 <barriered_thread>:
void* barriered_thread(void *arg) {
    33b0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    33b4:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
    33b8:	0f 85 90 02 00 00    	jne    364e <barriered_thread+0x29e>
void* barriered_thread(void *arg) {
    33be:	41 56                	push   %r14
    33c0:	41 55                	push   %r13
    33c2:	49 89 fd             	mov    %rdi,%r13
    33c5:	41 54                	push   %r12
    33c7:	55                   	push   %rbp
    33c8:	31 ed                	xor    %ebp,%ebp
    33ca:	53                   	push   %rbx
    33cb:	31 db                	xor    %ebx,%ebx
    33cd:	0f 1f 00             	nopl   (%rax)
    if (t >= data->task_count) {
    33d0:	41 8b 45 28          	mov    0x28(%r13),%eax
    33d4:	39 d8                	cmp    %ebx,%eax
    33d6:	7f 12                	jg     33ea <barriered_thread+0x3a>
      data->cycles++;
    33d8:	49 83 85 90 00 00 00 01 	addq   $0x1,0x90(%r13)
    for (; t < data->task_count; t++) {
    33e0:	31 db                	xor    %ebx,%ebx
    33e2:	85 c0                	test   %eax,%eax
    33e4:	0f 8e 66 01 00 00    	jle    3550 <barriered_thread+0x1a0>
    33ea:	4c 63 e3             	movslq %ebx,%r12
    33ed:	49 c1 e4 09          	shl    $0x9,%r12
    33f1:	eb 17                	jmp    340a <barriered_thread+0x5a>
    33f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    33f8:	83 c3 01             	add    $0x1,%ebx
    33fb:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    3402:	39 c3                	cmp    %eax,%ebx
    3404:	0f 8d 46 01 00 00    	jge    3550 <barriered_thread+0x1a0>
      if (data->tasks[t].available == 1) {
    340a:	49 8b 55 20          	mov    0x20(%r13),%rdx
    340e:	42 83 bc 22 80 01 00 00 01 	cmpl   $0x1,0x180(%rdx,%r12,1)
    3417:	75 df                	jne    33f8 <barriered_thread+0x48>
          previous = t - 1;
    3419:	8d 53 ff             	lea    -0x1(%rbx),%edx
    341c:	83 e8 01             	sub    $0x1,%eax
    341f:	85 db                	test   %ebx,%ebx
    3421:	0f 4f c2             	cmovg  %edx,%eax
        asm volatile ("sfence" ::: "memory");
    3424:	0f ae f8             	sfence
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3427:	45 8b 55 18          	mov    0x18(%r13),%r10d
    342b:	45 85 d2             	test   %r10d,%r10d
    342e:	0f 8e 4c 01 00 00    	jle    3580 <barriered_thread+0x1d0>
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    3434:	48 63 c8             	movslq %eax,%rcx
    3437:	49 8b 45 20          	mov    0x20(%r13),%rax
    343b:	49 63 d2             	movslq %r10d,%rdx
        int prearrive = 0; 
    343e:	45 31 c9             	xor    %r9d,%r9d
    3441:	48 8d 34 d2          	lea    (%rdx,%rdx,8),%rsi
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    3445:	48 c1 e1 09          	shl    $0x9,%rcx
        int arrived = 0; 
    3449:	45 31 f6             	xor    %r14d,%r14d
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    344c:	4c 01 e0             	add    %r12,%rax
    344f:	48 8d 14 72          	lea    (%rdx,%rsi,2),%rdx
    3453:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
          if (data->threads[thread].tasks[previous].prearrive == data->tasks[t].prearrive) {
    345a:	8b b8 00 01 00 00    	mov    0x100(%rax),%edi
    3460:	49 8b 45 10          	mov    0x10(%r13),%rax
    3464:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3468:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    3470:	48 8b 50 20          	mov    0x20(%rax),%rdx
    3474:	48 01 ca             	add    %rcx,%rdx
    3477:	44 3b 82 80 00 00 00 	cmp    0x80(%rdx),%r8d
    347e:	75 04                	jne    3484 <barriered_thread+0xd4>
            arrived++;
    3480:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread].tasks[previous].prearrive == data->tasks[t].prearrive) {
    3484:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    348a:	75 04                	jne    3490 <barriered_thread+0xe0>
            prearrive++;
    348c:	41 83 c1 01          	add    $0x1,%r9d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3490:	48 05 98 00 00 00    	add    $0x98,%rax
    3496:	48 39 f0             	cmp    %rsi,%rax
    3499:	75 d5                	jne    3470 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    349b:	45 39 ca             	cmp    %r9d,%r10d
    349e:	0f 84 cc 00 00 00    	je     3570 <barriered_thread+0x1c0>
    34a4:	45 85 c9             	test   %r9d,%r9d
    34a7:	0f 84 c3 00 00 00    	je     3570 <barriered_thread+0x1c0>
        if (arrived == 0 || arrived == data->thread_count) {
    34ad:	45 85 f6             	test   %r14d,%r14d
    34b0:	74 0a                	je     34bc <barriered_thread+0x10c>
    34b2:	45 39 75 18          	cmp    %r14d,0x18(%r13)
    34b6:	0f 85 94 00 00 00    	jne    3550 <barriered_thread+0x1a0>
          data->tasks[t].prearrive++;
    34bc:	49 8b 55 20          	mov    0x20(%r13),%rdx
    34c0:	4c 01 e2             	add    %r12,%rdx
    34c3:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    34ca:	85 db                	test   %ebx,%ebx
    34cc:	75 0e                	jne    34dc <barriered_thread+0x12c>
    34ce:	49 8b 75 68          	mov    0x68(%r13),%rsi
    34d2:	49 3b 75 70          	cmp    0x70(%r13),%rsi
    34d6:	0f 8c 54 01 00 00    	jl     3630 <barriered_thread+0x280>
          data->tasks[t].available = 0;
    34dc:	c7 82 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index].tasks[t]);
    34e6:	49 63 45 00          	movslq 0x0(%r13),%rax
    34ea:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    34ee:	48 8d 04 48          	lea    (%rax,%rcx,2),%rax
    34f2:	49 8b 4d 10          	mov    0x10(%r13),%rcx
    34f6:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    34fa:	48 8b 78 20          	mov    0x20(%rax),%rdi
    34fe:	4c 01 e7             	add    %r12,%rdi
    3501:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    3507:	49 8b 45 20          	mov    0x20(%r13),%rax
    350b:	4c 01 e0             	add    %r12,%rax
    350e:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          asm volatile ("sfence" ::: "memory");
    3515:	0f ae f8             	sfence
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3518:	41 8b 45 28          	mov    0x28(%r13),%eax
          data->iteration_count++;
    351c:	49 83 45 60 01       	addq   $0x1,0x60(%r13)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3521:	83 e8 01             	sub    $0x1,%eax
    3524:	39 d8                	cmp    %ebx,%eax
    3526:	0f 84 a4 00 00 00    	je     35d0 <barriered_thread+0x220>
          if (waiting == 0) {
    352c:	85 ed                	test   %ebp,%ebp
    352e:	0f 84 cc 00 00 00    	je     3600 <barriered_thread+0x250>
    for (; t < data->task_count; t++) {
    3534:	41 8b 45 28          	mov    0x28(%r13),%eax
    3538:	83 c3 01             	add    $0x1,%ebx
    353b:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    3542:	39 c3                	cmp    %eax,%ebx
    3544:	0f 8c c0 fe ff ff    	jl     340a <barriered_thread+0x5a>
    354a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  while (data->running == 1) {
    3550:	41 83 7d 2c 01       	cmpl   $0x1,0x2c(%r13)
    3555:	0f 84 75 fe ff ff    	je     33d0 <barriered_thread+0x20>
}
    355b:	5b                   	pop    %rbx
    355c:	31 c0                	xor    %eax,%eax
    355e:	5d                   	pop    %rbp
    355f:	41 5c                	pop    %r12
    3561:	41 5d                	pop    %r13
    3563:	41 5e                	pop    %r14
    3565:	c3                   	ret
    3566:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (waiting == 1) {
    3570:	83 fd 01             	cmp    $0x1,%ebp
    3573:	74 1b                	je     3590 <barriered_thread+0x1e0>
        int arrived = 0; 
    3575:	31 ed                	xor    %ebp,%ebp
    3577:	e9 31 ff ff ff       	jmp    34ad <barriered_thread+0xfd>
    357c:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    3580:	83 fd 01             	cmp    $0x1,%ebp
    3583:	0f 85 33 ff ff ff    	jne    34bc <barriered_thread+0x10c>
        int arrived = 0; 
    3589:	45 31 f6             	xor    %r14d,%r14d
    358c:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3590:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    3597:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    359c:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    359e:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    35a2:	49 8b 45 78          	mov    0x78(%r13),%rax
    35a6:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    35ab:	e8 40 ed ff ff       	call   22f0 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    35b0:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
    35b7:	48 83 c0 01          	add    $0x1,%rax
    35bb:	48 99                	cqto
    35bd:	49 f7 bd 88 00 00 00 	idivq  0x88(%r13)
    35c4:	49 89 95 80 00 00 00 	mov    %rdx,0x80(%r13)
            waiting = 0;
    35cb:	e9 dd fe ff ff       	jmp    34ad <barriered_thread+0xfd>
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    35d0:	49 8b 75 68          	mov    0x68(%r13),%rsi
    35d4:	49 3b 75 70          	cmp    0x70(%r13),%rsi
    35d8:	0f 8d 4e ff ff ff    	jge    352c <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    35de:	48 c1 e6 04          	shl    $0x4,%rsi
    35e2:	bf 04 00 00 00       	mov    $0x4,%edi
    35e7:	49 03 75 58          	add    0x58(%r13),%rsi
    35eb:	e8 00 ed ff ff       	call   22f0 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    35f0:	49 83 45 68 01       	addq   $0x1,0x68(%r13)
          if (waiting == 0) {
    35f5:	85 ed                	test   %ebp,%ebp
    35f7:	0f 85 37 ff ff ff    	jne    3534 <barriered_thread+0x184>
    35fd:	0f 1f 00             	nopl   (%rax)
            data->task_snapshot[data->task_timestamp_count].task = t;
    3600:	49 8b 85 80 00 00 00 	mov    0x80(%r13),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3607:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    360c:	bd 01 00 00 00       	mov    $0x1,%ebp
            data->task_snapshot[data->task_timestamp_count].task = t;
    3611:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3615:	49 8b 45 78          	mov    0x78(%r13),%rax
    3619:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    361d:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3620:	e8 cb ec ff ff       	call   22f0 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    3625:	41 8b 45 28          	mov    0x28(%r13),%eax
    3629:	e9 ca fd ff ff       	jmp    33f8 <barriered_thread+0x48>
    362e:	66 90                	xchg   %ax,%ax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3630:	48 c1 e6 04          	shl    $0x4,%rsi
    3634:	bf 04 00 00 00       	mov    $0x4,%edi
    3639:	49 03 75 50          	add    0x50(%r13),%rsi
    363d:	e8 ae ec ff ff       	call   22f0 <clock_gettime@plt>
          data->tasks[t].available = 0;
    3642:	49 8b 55 20          	mov    0x20(%r13),%rdx
    3646:	4c 01 e2             	add    %r12,%rdx
    3649:	e9 8e fe ff ff       	jmp    34dc <barriered_thread+0x12c>
}
    364e:	31 c0                	xor    %eax,%eax
    3650:	c3                   	ret
    3651:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    365c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003660 <external_thread>:
void * external_thread(void *arg) {
    3660:	f3 0f 1e fa          	endbr64
    3664:	41 55                	push   %r13
    3666:	41 54                	push   %r12
    3668:	55                   	push   %rbp
    3669:	53                   	push   %rbx
    366a:	48 83 ec 38          	sub    $0x38,%rsp
  struct timespec req = {
    366e:	66 0f 6f 05 7a 32 00 00 	movdqa 0x327a(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
void * external_thread(void *arg) {
    3676:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    367f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3684:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
    3686:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
  struct timespec req = {
    368a:	0f 29 04 24          	movaps %xmm0,(%rsp)
  while (data->running == 1) {
    368e:	75 64                	jne    36f4 <external_thread+0x94>
    3690:	49 89 fd             	mov    %rdi,%r13
    3693:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3698:	48 89 e3             	mov    %rsp,%rbx
        data->buffers->buffer[x].data = "Hello world";
    369b:	4c 8d 25 62 29 00 00 	lea    0x2962(%rip),%r12        # 6004 <_IO_stdin_used+0x4>
    36a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    nanosleep(&req , &rem);
    36a8:	48 89 ee             	mov    %rbp,%rsi
    36ab:	48 89 df             	mov    %rbx,%rdi
    36ae:	e8 7d ec ff ff       	call   2330 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    36b3:	49 8b 45 38          	mov    0x38(%r13),%rax
    36b7:	48 63 10             	movslq (%rax),%rdx
    36ba:	85 d2                	test   %edx,%edx
    36bc:	7e 2c                	jle    36ea <external_thread+0x8a>
    36be:	48 8b 40 08          	mov    0x8(%rax),%rax
    36c2:	48 c1 e2 04          	shl    $0x4,%rdx
    36c6:	48 01 c2             	add    %rax,%rdx
    36c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    36d0:	8b 48 08             	mov    0x8(%rax),%ecx
    36d3:	85 c9                	test   %ecx,%ecx
    36d5:	75 0a                	jne    36e1 <external_thread+0x81>
        data->buffers->buffer[x].data = "Hello world";
    36d7:	4c 89 20             	mov    %r12,(%rax)
        data->buffers->buffer[x].available = 1;
    36da:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    36e1:	48 83 c0 10          	add    $0x10,%rax
    36e5:	48 39 c2             	cmp    %rax,%rdx
    36e8:	75 e6                	jne    36d0 <external_thread+0x70>
    asm volatile ("mfence" ::: "memory");
    36ea:	0f ae f0             	mfence
  while (data->running == 1) {
    36ed:	41 83 7d 2c 01       	cmpl   $0x1,0x2c(%r13)
    36f2:	74 b4                	je     36a8 <external_thread+0x48>
}
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
void* timer_thread(void *arg) {
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
  struct timespec preempt = {
    3758:	66 0f 6f 05 90 31 00 00 	movdqa 0x3190(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
    3760:	ba 10 27 00 00       	mov    $0x2710,%edx
    3765:	31 c0                	xor    %eax,%eax
    3767:	48 8d 35 b4 28 00 00 	lea    0x28b4(%rip),%rsi        # 6022 <_IO_stdin_used+0x22>
    376e:	bf 01 00 00 00       	mov    $0x1,%edi
    3773:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3778:	e8 b3 ec ff ff       	call   2430 <__printf_chk@plt>
  while (data->running && n < times) {
    377d:	45 8b 67 2c          	mov    0x2c(%r15),%r12d
    3781:	45 85 e4             	test   %r12d,%r12d
    3784:	0f 84 9f 00 00 00    	je     3829 <timer_thread+0x109>
  int n = 0;
    378a:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    378d:	45 31 e4             	xor    %r12d,%r12d
    3790:	49 89 e5             	mov    %rsp,%r13
    y++;
    3793:	31 db                	xor    %ebx,%ebx
    3795:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    379a:	48 89 ef             	mov    %rbp,%rdi
    379d:	4c 89 ee             	mov    %r13,%rsi
    n++;
    37a0:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    37a4:	e8 87 eb ff ff       	call   2330 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    37a9:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    37ad:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    37b2:	85 c0                	test   %eax,%eax
    37b4:	7e 4e                	jle    3804 <timer_thread+0xe4>
    37b6:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    37ba:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
        data->threads[x].tasks[y].scheduled = 0;
    37be:	49 c1 e4 09          	shl    $0x9,%r12
    37c2:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    37c6:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    37ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x].task_count;
    37d0:	89 f8                	mov    %edi,%eax
        data->threads[x].tasks[next].scheduled = 1;
    37d2:	48 8b 71 20          	mov    0x20(%rcx),%rsi
        int next = (y + 1) % data->threads[x].task_count;
    37d6:	99                   	cltd
    37d7:	f7 79 28             	idivl  0x28(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    37da:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
        data->threads[x].tasks[next].scheduled = 1;
    37e1:	48 63 d2             	movslq %edx,%rdx
    37e4:	48 c1 e2 09          	shl    $0x9,%rdx
    37e8:	c7 84 16 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rsi,%rdx,1)
        data->threads[x].tasks[y].scheduled = 0;
    37f3:	42 c7 84 26 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rsi,%r12,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    37ff:	49 39 c8             	cmp    %rcx,%r8
    3802:	75 cc                	jne    37d0 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
    3804:	0f ae f0             	mfence
    if (y >= data->threads[0].task_count) {
    3807:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
    380b:	41 8b 57 2c          	mov    0x2c(%r15),%edx
    y++;
    380f:	39 78 28             	cmp    %edi,0x28(%rax)
    3812:	0f 4e fb             	cmovle %ebx,%edi
    3815:	4c 63 e7             	movslq %edi,%r12
  while (data->running && n < times) {
    3818:	85 d2                	test   %edx,%edx
    381a:	74 0d                	je     3829 <timer_thread+0x109>
    381c:	41 81 fe 10 27 00 00 	cmp    $0x2710,%r14d
    3823:	0f 85 71 ff ff ff    	jne    379a <timer_thread+0x7a>
    3829:	48 8d 3d 08 28 00 00 	lea    0x2808(%rip),%rdi        # 6038 <_IO_stdin_used+0x38>
    3830:	e8 9b ea ff ff       	call   22d0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3835:	49 63 57 1c          	movslq 0x1c(%r15),%rdx
    3839:	85 d2                	test   %edx,%edx
    383b:	7e 6c                	jle    38a9 <timer_thread+0x189>
    for (int y = 0 ; y < data->task_count ; y++) {
    383d:	49 63 47 28          	movslq 0x28(%r15),%rax
    3841:	85 c0                	test   %eax,%eax
    3843:	7e 64                	jle    38a9 <timer_thread+0x189>
    3845:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    3849:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x].tasks[y].sending = 0;
    384d:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3851:	31 f6                	xor    %esi,%esi
    3853:	48 8d 3c 4a          	lea    (%rdx,%rcx,2),%rdi
    3857:	48 89 c2             	mov    %rax,%rdx
    385a:	48 c1 e7 03          	shl    $0x3,%rdi
    for (int y = 0 ; y < data->task_count ; y++) {
    385e:	49 8b 44 30 20       	mov    0x20(%r8,%rsi,1),%rax
    3863:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    3867:	f6 c6 02             	test   $0x2,%dh
    386a:	74 15                	je     3881 <timer_thread+0x161>
      data->threads[x].tasks[y].sending = 0;
    386c:	c7 80 c0 01 00 00 00 00 00 00 	movl   $0x0,0x1c0(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3876:	48 05 00 02 00 00    	add    $0x200,%rax
    387c:	48 39 c1             	cmp    %rax,%rcx
    387f:	74 1c                	je     389d <timer_thread+0x17d>
      data->threads[x].tasks[y].sending = 0;
    3881:	c7 80 c0 01 00 00 00 00 00 00 	movl   $0x0,0x1c0(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    388b:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x].tasks[y].sending = 0;
    3891:	c7 40 c0 00 00 00 00 	movl   $0x0,-0x40(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3898:	48 39 c1             	cmp    %rax,%rcx
    389b:	75 e4                	jne    3881 <timer_thread+0x161>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    389d:	48 81 c6 98 00 00 00 	add    $0x98,%rsi
    38a4:	48 39 f7             	cmp    %rsi,%rdi
    38a7:	75 b5                	jne    385e <timer_thread+0x13e>
  asm volatile ("mfence" ::: "memory");
    38a9:	0f ae f0             	mfence
  struct timespec drain = {
    38ac:	66 0f 6f 05 4c 30 00 00 	movdqa 0x304c(%rip),%xmm0        # 6900 <_IO_stdin_used+0x900>
    38b4:	48 8d 2d a2 27 00 00 	lea    0x27a2(%rip),%rbp        # 605d <_IO_stdin_used+0x5d>
    38bb:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    38c0:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    38c4:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    38c9:	85 c0                	test   %eax,%eax
    38cb:	7e 4f                	jle    391c <timer_thread+0x1fc>
    38cd:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    38d1:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
        data->threads[x].tasks[y].scheduled = 0;
    38d5:	4d 63 c4             	movslq %r12d,%r8
    38d8:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    38dc:	49 c1 e0 09          	shl    $0x9,%r8
    38e0:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    38e4:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x].task_count;
    38e8:	89 f8                	mov    %edi,%eax
        data->threads[x].tasks[next].scheduled = 1;
    38ea:	48 8b 71 20          	mov    0x20(%rcx),%rsi
        int next = (y + 1) % data->threads[x].task_count;
    38ee:	99                   	cltd
    38ef:	f7 79 28             	idivl  0x28(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    38f2:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
        data->threads[x].tasks[next].scheduled = 1;
    38f9:	48 63 d2             	movslq %edx,%rdx
    38fc:	48 c1 e2 09          	shl    $0x9,%rdx
    3900:	c7 84 16 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rsi,%rdx,1)
        data->threads[x].tasks[y].scheduled = 0;
    390b:	42 c7 84 06 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3917:	49 39 c9             	cmp    %rcx,%r9
    391a:	75 cc                	jne    38e8 <timer_thread+0x1c8>
    asm volatile ("mfence" ::: "memory");
    391c:	0f ae f0             	mfence
    if (y >= data->threads[0].task_count) {
    391f:	49 8b 57 10          	mov    0x10(%r15),%rdx
    y++;
    3923:	45 31 e4             	xor    %r12d,%r12d
    3926:	39 7a 28             	cmp    %edi,0x28(%rdx)
    3929:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->thread_count ; x++) {
    392d:	41 8b 7f 18          	mov    0x18(%r15),%edi
    3931:	85 ff                	test   %edi,%edi
    3933:	0f 8e ba 00 00 00    	jle    39f3 <timer_thread+0x2d3>
    3939:	31 db                	xor    %ebx,%ebx
    393b:	45 31 ed             	xor    %r13d,%r13d
    393e:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3944:	0f 1f 40 00          	nopl   0x0(%rax)
            all_empty = 0;
    3948:	45 31 f6             	xor    %r14d,%r14d
    394b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3950:	4c 89 f0             	mov    %r14,%rax
    3953:	48 c1 e0 09          	shl    $0x9,%rax
    3957:	48 03 44 1a 20       	add    0x20(%rdx,%rbx,1),%rax
        for (int k = 0 ; k < data->thread_count; k++) {
    395c:	31 d2                	xor    %edx,%edx
    395e:	48 8b 80 b0 01 00 00 	mov    0x1b0(%rax),%rax
    3965:	eb 19                	jmp    3980 <timer_thread+0x260>
    3967:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3970:	4d 85 c0             	test   %r8,%r8
    3973:	7f 1f                	jg     3994 <timer_thread+0x274>
        for (int k = 0 ; k < data->thread_count; k++) {
    3975:	83 c2 01             	add    $0x1,%edx
    3978:	48 83 c0 20          	add    $0x20,%rax
    397c:	39 fa                	cmp    %edi,%edx
    397e:	74 2a                	je     39aa <timer_thread+0x28a>
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3980:	48 8b 08             	mov    (%rax),%rcx
    3983:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3987:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    398b:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    398f:	48 85 c9             	test   %rcx,%rcx
    3992:	7e dc                	jle    3970 <timer_thread+0x250>
    3994:	bf 01 00 00 00       	mov    $0x1,%edi
    3999:	48 89 ee             	mov    %rbp,%rsi
    399c:	31 c0                	xor    %eax,%eax
    399e:	e8 8d ea ff ff       	call   2430 <__printf_chk@plt>
            break;
    39a3:	41 8b 7f 18          	mov    0x18(%r15),%edi
            all_empty = 0;
    39a7:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->thread_count ; y++) {
    39aa:	49 83 c6 01          	add    $0x1,%r14
    39ae:	44 39 f7             	cmp    %r14d,%edi
    39b1:	7e 0d                	jle    39c0 <timer_thread+0x2a0>
    39b3:	49 8b 57 10          	mov    0x10(%r15),%rdx
    39b7:	eb 97                	jmp    3950 <timer_thread+0x230>
    39b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->thread_count ; x++) {
    39c0:	41 83 c5 01          	add    $0x1,%r13d
    39c4:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    39cb:	44 39 ef             	cmp    %r13d,%edi
    39ce:	7e 09                	jle    39d9 <timer_thread+0x2b9>
    39d0:	49 8b 57 10          	mov    0x10(%r15),%rdx
    39d4:	e9 6f ff ff ff       	jmp    3948 <timer_thread+0x228>
    if (all_empty == 1) {
    39d9:	41 83 f9 01          	cmp    $0x1,%r9d
    39dd:	74 14                	je     39f3 <timer_thread+0x2d3>
      nanosleep(&drain , &drainrem);
    39df:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    39e4:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    39e9:	e8 42 e9 ff ff       	call   2330 <nanosleep@plt>
    39ee:	e9 cd fe ff ff       	jmp    38c0 <timer_thread+0x1a0>
    39f3:	48 8d 3d 5a 26 00 00 	lea    0x265a(%rip),%rdi        # 6054 <_IO_stdin_used+0x54>
    39fa:	e8 d1 e8 ff ff       	call   22d0 <puts@plt>
  while (data->running) {
    39ff:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    3a03:	85 c0                	test   %eax,%eax
    3a05:	0f 84 d4 00 00 00    	je     3adf <timer_thread+0x3bf>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3a0b:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3a0f:	85 c9                	test   %ecx,%ecx
    3a11:	7e 38                	jle    3a4b <timer_thread+0x32b>
    3a13:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3a17:	31 db                	xor    %ebx,%ebx
    3a19:	31 ed                	xor    %ebp,%ebp
    3a1b:	4c 8d 25 4c 26 00 00 	lea    0x264c(%rip),%r12        # 606e <_IO_stdin_used+0x6e>
    3a22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->threads[x].running = 0;
    3a28:	48 8d 04 1a          	lea    (%rdx,%rbx,1),%rax
      if (data->threads[x].type == IO) {
    3a2c:	83 78 04 02          	cmpl   $0x2,0x4(%rax)
      data->threads[x].running = 0;
    3a30:	c7 40 2c 00 00 00 00 	movl   $0x0,0x2c(%rax)
      if (data->threads[x].type == IO) {
    3a37:	0f 84 cf 00 00 00    	je     3b0c <timer_thread+0x3ec>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3a3d:	83 c5 01             	add    $0x1,%ebp
    3a40:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3a47:	39 cd                	cmp    %ecx,%ebp
    3a49:	7c dd                	jl     3a28 <timer_thread+0x308>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a4b:	49 63 57 18          	movslq 0x18(%r15),%rdx
    3a4f:	85 d2                	test   %edx,%edx
    3a51:	7e 75                	jle    3ac8 <timer_thread+0x3a8>
      for (int y = 0 ; y < data->task_count ; y++) {
    3a53:	49 63 47 28          	movslq 0x28(%r15),%rax
    3a57:	85 c0                	test   %eax,%eax
    3a59:	7e 6d                	jle    3ac8 <timer_thread+0x3a8>
    3a5b:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    3a5f:	48 c1 e0 09          	shl    $0x9,%rax
        data->threads[x].tasks[y].scheduled = 0;
    3a63:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3a67:	48 8d 3c 4a          	lea    (%rdx,%rcx,2),%rdi
    3a6b:	48 89 c6             	mov    %rax,%rsi
    3a6e:	31 c9                	xor    %ecx,%ecx
    3a70:	48 c1 e7 03          	shl    $0x3,%rdi
    3a74:	0f 1f 40 00          	nopl   0x0(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3a78:	49 8b 44 08 20       	mov    0x20(%r8,%rcx,1),%rax
    3a7d:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3a81:	f7 c6 00 02 00 00    	test   $0x200,%esi
    3a87:	74 17                	je     3aa0 <timer_thread+0x380>
        data->threads[x].tasks[y].scheduled = 0;
    3a89:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3a93:	48 05 00 02 00 00    	add    $0x200,%rax
    3a99:	48 39 d0             	cmp    %rdx,%rax
    3a9c:	74 1e                	je     3abc <timer_thread+0x39c>
    3a9e:	66 90                	xchg   %ax,%ax
        data->threads[x].tasks[y].scheduled = 0;
    3aa0:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3aaa:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x].tasks[y].scheduled = 0;
    3ab0:	c7 40 88 00 00 00 00 	movl   $0x0,-0x78(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3ab7:	48 39 d0             	cmp    %rdx,%rax
    3aba:	75 e4                	jne    3aa0 <timer_thread+0x380>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3abc:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3ac3:	48 39 f9             	cmp    %rdi,%rcx
    3ac6:	75 b0                	jne    3a78 <timer_thread+0x358>
    asm volatile ("mfence" ::: "memory");
    3ac8:	0f ae f0             	mfence
    3acb:	48 8d 3d ae 25 00 00 	lea    0x25ae(%rip),%rdi        # 6080 <_IO_stdin_used+0x80>
    3ad2:	e8 f9 e7 ff ff       	call   22d0 <puts@plt>
    data->running = 0;
    3ad7:	41 c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%r15)
    3adf:	48 8d 3d a1 25 00 00 	lea    0x25a1(%rip),%rdi        # 6087 <_IO_stdin_used+0x87>
    3ae6:	e8 e5 e7 ff ff       	call   22d0 <puts@plt>
}
    3aeb:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3af0:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3af9:	75 4a                	jne    3b45 <timer_thread+0x425>
    3afb:	48 83 c4 58          	add    $0x58,%rsp
    3aff:	31 c0                	xor    %eax,%eax
    3b01:	5b                   	pop    %rbx
    3b02:	5d                   	pop    %rbp
    3b03:	41 5c                	pop    %r12
    3b05:	41 5d                	pop    %r13
    3b07:	41 5e                	pop    %r14
    3b09:	41 5f                	pop    %r15
    3b0b:	c3                   	ret
    3b0c:	4c 89 e7             	mov    %r12,%rdi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b0f:	83 c5 01             	add    $0x1,%ebp
    3b12:	e8 b9 e7 ff ff       	call   22d0 <puts@plt>
        eventfd_write(data->threads[x]._eventfd, 1);
    3b17:	49 8b 47 10          	mov    0x10(%r15),%rax
    3b1b:	be 01 00 00 00       	mov    $0x1,%esi
    3b20:	8b 7c 18 48          	mov    0x48(%rax,%rbx,1),%edi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b24:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
        eventfd_write(data->threads[x]._eventfd, 1);
    3b2b:	e8 b0 e8 ff ff       	call   23e0 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b30:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3b34:	39 cd                	cmp    %ecx,%ebp
    3b36:	0f 8d 0f ff ff ff    	jge    3a4b <timer_thread+0x32b>
    3b3c:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3b40:	e9 e3 fe ff ff       	jmp    3a28 <timer_thread+0x308>
}
    3b45:	e8 c6 e7 ff ff       	call   2310 <__stack_chk_fail@plt>
    3b4a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000003b50 <strtolower>:
void strtolower(char *str) {
    3b50:	f3 0f 1e fa          	endbr64
    3b54:	55                   	push   %rbp
    3b55:	53                   	push   %rbx
    3b56:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    3b5a:	48 0f be 1f          	movsbq (%rdi),%rbx
    3b5e:	84 db                	test   %bl,%bl
    3b60:	74 24                	je     3b86 <strtolower+0x36>
    3b62:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    3b65:	e8 86 e9 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3b6a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3b70:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3b73:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    3b77:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3b7a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    3b7d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3b82:	84 db                	test   %bl,%bl
    3b84:	75 ea                	jne    3b70 <strtolower+0x20>
}
    3b86:	48 83 c4 08          	add    $0x8,%rsp
    3b8a:	5b                   	pop    %rbx
    3b8b:	5d                   	pop    %rbp
    3b8c:	c3                   	ret
    3b8d:	0f 1f 00             	nopl   (%rax)

0000000000003b90 <zh_malloc>:
void *zh_malloc(size_t size) {
    3b90:	f3 0f 1e fa          	endbr64
    3b94:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    3b98:	e8 53 e8 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3b9d:	48 85 c0             	test   %rax,%rax
    3ba0:	74 05                	je     3ba7 <zh_malloc+0x17>
}
    3ba2:	48 83 c4 08          	add    $0x8,%rsp
    3ba6:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3ba7:	48 8b 0d 72 54 00 00 	mov    0x5472(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    3bae:	ba 28 00 00 00       	mov    $0x28,%edx
    3bb3:	be 01 00 00 00       	mov    $0x1,%esi
    3bb8:	48 8d 3d 61 28 00 00 	lea    0x2861(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    3bbf:	e8 dc e8 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    3bc4:	bf 01 00 00 00       	mov    $0x1,%edi
    3bc9:	e8 b2 e8 ff ff       	call   2480 <exit@plt>
    3bce:	66 90                	xchg   %ax,%ax

0000000000003bd0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3bd0:	f3 0f 1e fa          	endbr64
    3bd4:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    3bd5:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3bda:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3bdd:	e8 5e e7 ff ff       	call   2340 <strrchr@plt>
    if (!dot || dot == filename)
    3be2:	48 85 c0             	test   %rax,%rax
    3be5:	74 11                	je     3bf8 <get_filename_ext+0x28>
    3be7:	48 39 c3             	cmp    %rax,%rbx
    3bea:	74 0c                	je     3bf8 <get_filename_ext+0x28>
    return dot + 1;
    3bec:	48 83 c0 01          	add    $0x1,%rax
}
    3bf0:	5b                   	pop    %rbx
    3bf1:	c3                   	ret
    3bf2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    3bf8:	48 8d 05 d0 24 00 00 	lea    0x24d0(%rip),%rax        # 60cf <_IO_stdin_used+0xcf>
}
    3bff:	5b                   	pop    %rbx
    3c00:	c3                   	ret
    3c01:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3c0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003c10 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    3c10:	f3 0f 1e fa          	endbr64
    3c14:	41 55                	push   %r13
    3c16:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3c19:	48 89 fe             	mov    %rdi,%rsi
    3c1c:	41 54                	push   %r12
    3c1e:	55                   	push   %rbp
    3c1f:	48 89 d5             	mov    %rdx,%rbp
    3c22:	ba 00 04 00 00       	mov    $0x400,%edx
    3c27:	53                   	push   %rbx
    3c28:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    3c2f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3c38:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3c40:	31 c0                	xor    %eax,%eax
    3c42:	49 89 e4             	mov    %rsp,%r12
    3c45:	4c 89 e7             	mov    %r12,%rdi
    3c48:	e8 c3 e7 ff ff       	call   2410 <__strcpy_chk@plt>
    for (; *str; ++str)
    3c4d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3c52:	84 db                	test   %bl,%bl
    3c54:	74 24                	je     3c7a <send_headers+0x6a>
        *str = (char)tolower(*str);
    3c56:	e8 95 e8 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3c5b:	48 8b 08             	mov    (%rax),%rcx
    3c5e:	4c 89 e0             	mov    %r12,%rax
    3c61:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3c68:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    3c6b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    3c6f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    3c72:	48 0f be 18          	movsbq (%rax),%rbx
    3c76:	84 db                	test   %bl,%bl
    3c78:	75 ee                	jne    3c68 <send_headers+0x58>
    void *buf = malloc(size);
    3c7a:	bf 11 00 00 00       	mov    $0x11,%edi
    3c7f:	e8 6c e7 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3c84:	48 85 c0             	test   %rax,%rax
    3c87:	0f 84 7e 04 00 00    	je     410b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3c8d:	66 0f 6f 05 7b 2c 00 00 	movdqa 0x2c7b(%rip),%xmm0        # 6910 <_IO_stdin_used+0x910>
    iov[0].iov_base = zh_malloc(slen);
    3c95:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    3c99:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    3c9e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3ca6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3caa:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    3cad:	e8 3e e7 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3cb2:	48 85 c0             	test   %rax,%rax
    3cb5:	0f 84 50 04 00 00    	je     410b <send_headers+0x4fb>
    3cbb:	66 0f 6f 05 5d 2c 00 00 	movdqa 0x2c5d(%rip),%xmm0        # 6920 <_IO_stdin_used+0x920>
    iov[1].iov_base = zh_malloc(slen);
    3cc3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    3cc7:	4c 89 e7             	mov    %r12,%rdi
    3cca:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    3cd4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    3cdc:	0f 11 00             	movups %xmm0,(%rax)
    3cdf:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    3ce3:	be 2e 00 00 00       	mov    $0x2e,%esi
    3ce8:	e8 53 e6 ff ff       	call   2340 <strrchr@plt>
    if (!dot || dot == filename)
    3ced:	48 85 c0             	test   %rax,%rax
    3cf0:	0f 84 ea 02 00 00    	je     3fe0 <send_headers+0x3d0>
    3cf6:	4c 39 e0             	cmp    %r12,%rax
    3cf9:	0f 84 e1 02 00 00    	je     3fe0 <send_headers+0x3d0>
    return dot + 1;
    3cff:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    3d03:	48 8d 3d 93 23 00 00 	lea    0x2393(%rip),%rdi        # 609d <_IO_stdin_used+0x9d>
    3d0a:	48 89 de             	mov    %rbx,%rsi
    3d0d:	e8 7e e6 ff ff       	call   2390 <strcmp@plt>
    3d12:	85 c0                	test   %eax,%eax
    3d14:	75 20                	jne    3d36 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3d16:	66 0f 6f 05 12 2c 00 00 	movdqa 0x2c12(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3d1e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3d26:	66 0f 6f 05 12 2c 00 00 	movdqa 0x2c12(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3d2e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    3d36:	48 89 de             	mov    %rbx,%rsi
    3d39:	48 8d 3d 61 23 00 00 	lea    0x2361(%rip),%rdi        # 60a1 <_IO_stdin_used+0xa1>
    3d40:	e8 4b e6 ff ff       	call   2390 <strcmp@plt>
    3d45:	85 c0                	test   %eax,%eax
    3d47:	75 20                	jne    3d69 <send_headers+0x159>
    3d49:	66 0f 6f 05 df 2b 00 00 	movdqa 0x2bdf(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3d51:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3d59:	66 0f 6f 05 df 2b 00 00 	movdqa 0x2bdf(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3d61:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    3d69:	48 89 de             	mov    %rbx,%rsi
    3d6c:	48 8d 3d 33 23 00 00 	lea    0x2333(%rip),%rdi        # 60a6 <_IO_stdin_used+0xa6>
    3d73:	e8 18 e6 ff ff       	call   2390 <strcmp@plt>
    3d78:	85 c0                	test   %eax,%eax
    3d7a:	0f 84 10 02 00 00    	je     3f90 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    3d80:	48 89 de             	mov    %rbx,%rsi
    3d83:	48 8d 3d 20 23 00 00 	lea    0x2320(%rip),%rdi        # 60aa <_IO_stdin_used+0xaa>
    3d8a:	e8 01 e6 ff ff       	call   2390 <strcmp@plt>
    3d8f:	85 c0                	test   %eax,%eax
    3d91:	0f 84 a9 02 00 00    	je     4040 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    3d97:	48 89 de             	mov    %rbx,%rsi
    3d9a:	48 8d 3d 0d 23 00 00 	lea    0x230d(%rip),%rdi        # 60ae <_IO_stdin_used+0xae>
    3da1:	e8 ea e5 ff ff       	call   2390 <strcmp@plt>
    3da6:	85 c0                	test   %eax,%eax
    3da8:	0f 84 6a 02 00 00    	je     4018 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    3dae:	48 89 de             	mov    %rbx,%rsi
    3db1:	48 8d 3d 39 23 00 00 	lea    0x2339(%rip),%rdi        # 60f1 <_IO_stdin_used+0xf1>
    3db8:	e8 d3 e5 ff ff       	call   2390 <strcmp@plt>
    3dbd:	85 c0                	test   %eax,%eax
    3dbf:	0f 84 2b 02 00 00    	je     3ff0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    3dc5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3dc8:	0f 84 52 01 00 00    	je     3f20 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    3dce:	48 89 de             	mov    %rbx,%rsi
    3dd1:	48 8d 3d da 22 00 00 	lea    0x22da(%rip),%rdi        # 60b2 <_IO_stdin_used+0xb2>
    3dd8:	e8 b3 e5 ff ff       	call   2390 <strcmp@plt>
    3ddd:	85 c0                	test   %eax,%eax
    3ddf:	0f 84 ab 02 00 00    	je     4090 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    3de5:	48 89 de             	mov    %rbx,%rsi
    3de8:	48 8d 3d c7 22 00 00 	lea    0x22c7(%rip),%rdi        # 60b6 <_IO_stdin_used+0xb6>
    3def:	e8 9c e5 ff ff       	call   2390 <strcmp@plt>
    3df4:	85 c0                	test   %eax,%eax
    3df6:	0f 84 6c 02 00 00    	je     4068 <send_headers+0x458>
    slen = strlen(send_buffer);
    3dfc:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    3e04:	4c 89 e7             	mov    %r12,%rdi
    3e07:	e8 f4 e4 ff ff       	call   2300 <strlen@plt>
    void *buf = malloc(size);
    3e0c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3e0f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    3e12:	e8 d9 e5 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3e17:	48 85 c0             	test   %rax,%rax
    3e1a:	0f 84 eb 02 00 00    	je     410b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    3e20:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    3e24:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    3e28:	83 fb 08             	cmp    $0x8,%ebx
    3e2b:	0f 83 3f 01 00 00    	jae    3f70 <send_headers+0x360>
    3e31:	f6 c3 04             	test   $0x4,%bl
    3e34:	0f 85 7b 02 00 00    	jne    40b5 <send_headers+0x4a5>
    3e3a:	85 db                	test   %ebx,%ebx
    3e3c:	74 13                	je     3e51 <send_headers+0x241>
    3e3e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3e46:	88 10                	mov    %dl,(%rax)
    3e48:	f6 c3 02             	test   $0x2,%bl
    3e4b:	0f 85 96 02 00 00    	jne    40e7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3e51:	4d 89 e8             	mov    %r13,%r8
    3e54:	48 8d 0d 5f 22 00 00 	lea    0x225f(%rip),%rcx        # 60ba <_IO_stdin_used+0xba>
    3e5b:	4c 89 e7             	mov    %r12,%rdi
    3e5e:	31 c0                	xor    %eax,%eax
    3e60:	ba 00 04 00 00       	mov    $0x400,%edx
    3e65:	be 01 00 00 00       	mov    $0x1,%esi
    3e6a:	e8 91 e6 ff ff       	call   2500 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    3e6f:	4c 89 e7             	mov    %r12,%rdi
    3e72:	e8 89 e4 ff ff       	call   2300 <strlen@plt>
    void *buf = malloc(size);
    3e77:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3e7a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    3e7d:	e8 6e e5 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3e82:	48 85 c0             	test   %rax,%rax
    3e85:	0f 84 80 02 00 00    	je     410b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    3e8b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    3e8f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    3e93:	83 fb 08             	cmp    $0x8,%ebx
    3e96:	0f 83 1c 01 00 00    	jae    3fb8 <send_headers+0x3a8>
    3e9c:	f6 c3 04             	test   $0x4,%bl
    3e9f:	0f 85 29 02 00 00    	jne    40ce <send_headers+0x4be>
    3ea5:	85 db                	test   %ebx,%ebx
    3ea7:	74 13                	je     3ebc <send_headers+0x2ac>
    3ea9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3eb1:	88 10                	mov    %dl,(%rax)
    3eb3:	f6 c3 02             	test   $0x2,%bl
    3eb6:	0f 85 3d 02 00 00    	jne    40f9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3ebc:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    3ec1:	bf 02 00 00 00       	mov    $0x2,%edi
    3ec6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    3ece:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    3ed6:	e8 15 e5 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3edb:	48 85 c0             	test   %rax,%rax
    3ede:	0f 84 27 02 00 00    	je     410b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3ee4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    3eec:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    3ef0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    3ef8:	66 89 10             	mov    %dx,(%rax)
}
    3efb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    3f03:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3f0c:	0f 85 20 02 00 00    	jne    4132 <send_headers+0x522>
    3f12:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    3f19:	5b                   	pop    %rbx
    3f1a:	5d                   	pop    %rbp
    3f1b:	41 5c                	pop    %r12
    3f1d:	41 5d                	pop    %r13
    3f1f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    3f20:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    3f24:	0f 85 a4 fe ff ff    	jne    3dce <send_headers+0x1be>
    3f2a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    3f2e:	0f 85 9a fe ff ff    	jne    3dce <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3f34:	66 0f 6f 05 54 2a 00 00 	movdqa 0x2a54(%rip),%xmm0        # 6990 <_IO_stdin_used+0x990>
    3f3c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    3f46:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3f4e:	66 0f 6f 05 4a 2a 00 00 	movdqa 0x2a4a(%rip),%xmm0        # 69a0 <_IO_stdin_used+0x9a0>
    3f56:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    3f5e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    3f66:	e9 63 fe ff ff       	jmp    3dce <send_headers+0x1be>
    3f6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    3f70:	89 da                	mov    %ebx,%edx
    3f72:	48 89 c7             	mov    %rax,%rdi
    3f75:	4c 89 e6             	mov    %r12,%rsi
    3f78:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    3f7d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    3f82:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    3f85:	c1 e9 03             	shr    $0x3,%ecx
    3f88:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    3f8b:	e9 c1 fe ff ff       	jmp    3e51 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3f90:	66 0f 6f 05 98 29 00 00 	movdqa 0x2998(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3f98:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3fa0:	66 0f 6f 05 a8 29 00 00 	movdqa 0x29a8(%rip),%xmm0        # 6950 <_IO_stdin_used+0x950>
    3fa8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    3fb0:	e9 cb fd ff ff       	jmp    3d80 <send_headers+0x170>
    3fb5:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    3fb8:	89 da                	mov    %ebx,%edx
    3fba:	48 89 c7             	mov    %rax,%rdi
    3fbd:	4c 89 e6             	mov    %r12,%rsi
    3fc0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    3fc5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    3fca:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    3fcd:	c1 e9 03             	shr    $0x3,%ecx
    3fd0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    3fd3:	e9 e4 fe ff ff       	jmp    3ebc <send_headers+0x2ac>
    3fd8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    3fe0:	48 8d 1d e8 20 00 00 	lea    0x20e8(%rip),%rbx        # 60cf <_IO_stdin_used+0xcf>
    3fe7:	e9 94 fd ff ff       	jmp    3d80 <send_headers+0x170>
    3fec:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3ff0:	66 0f 6f 05 78 29 00 00 	movdqa 0x2978(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    3ff8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4000:	66 0f 6f 05 78 29 00 00 	movdqa 0x2978(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    4008:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4010:	e9 b0 fd ff ff       	jmp    3dc5 <send_headers+0x1b5>
    4015:	0f 1f 00             	nopl   (%rax)
    4018:	66 0f 6f 05 50 29 00 00 	movdqa 0x2950(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4020:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4028:	66 0f 6f 05 50 29 00 00 	movdqa 0x2950(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    4030:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4038:	e9 71 fd ff ff       	jmp    3dae <send_headers+0x19e>
    403d:	0f 1f 00             	nopl   (%rax)
    4040:	66 0f 6f 05 e8 28 00 00 	movdqa 0x28e8(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    4048:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4050:	66 0f 6f 05 08 29 00 00 	movdqa 0x2908(%rip),%xmm0        # 6960 <_IO_stdin_used+0x960>
    4058:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4060:	e9 32 fd ff ff       	jmp    3d97 <send_headers+0x187>
    4065:	0f 1f 00             	nopl   (%rax)
    4068:	66 0f 6f 05 00 29 00 00 	movdqa 0x2900(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4070:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4078:	66 0f 6f 05 40 29 00 00 	movdqa 0x2940(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    4080:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4088:	e9 6f fd ff ff       	jmp    3dfc <send_headers+0x1ec>
    408d:	0f 1f 00             	nopl   (%rax)
    4090:	66 0f 6f 05 d8 28 00 00 	movdqa 0x28d8(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4098:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40a0:	66 0f 6f 05 08 29 00 00 	movdqa 0x2908(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    40a8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    40b0:	e9 30 fd ff ff       	jmp    3de5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    40b5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    40bc:	89 db                	mov    %ebx,%ebx
    40be:	89 10                	mov    %edx,(%rax)
    40c0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    40c5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    40c9:	e9 83 fd ff ff       	jmp    3e51 <send_headers+0x241>
    40ce:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    40d5:	89 db                	mov    %ebx,%ebx
    40d7:	89 10                	mov    %edx,(%rax)
    40d9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    40de:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    40e2:	e9 d5 fd ff ff       	jmp    3ebc <send_headers+0x2ac>
    40e7:	89 db                	mov    %ebx,%ebx
    40e9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    40ef:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    40f4:	e9 58 fd ff ff       	jmp    3e51 <send_headers+0x241>
    40f9:	89 db                	mov    %ebx,%ebx
    40fb:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4101:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4106:	e9 b1 fd ff ff       	jmp    3ebc <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    410b:	48 8b 0d 0e 4f 00 00 	mov    0x4f0e(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4112:	ba 28 00 00 00       	mov    $0x28,%edx
    4117:	be 01 00 00 00       	mov    $0x1,%esi
    411c:	48 8d 3d fd 22 00 00 	lea    0x22fd(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    4123:	e8 78 e3 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    4128:	bf 01 00 00 00       	mov    $0x1,%edi
    412d:	e8 4e e3 ff ff       	call   2480 <exit@plt>
}
    4132:	e8 d9 e1 ff ff       	call   2310 <__stack_chk_fail@plt>
    4137:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004140 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4140:	f3 0f 1e fa          	endbr64
    4144:	41 55                	push   %r13
    4146:	49 89 d5             	mov    %rdx,%r13
    4149:	41 54                	push   %r12
    414b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    414e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4151:	55                   	push   %rbp
    4152:	53                   	push   %rbx
    4153:	48 89 f3             	mov    %rsi,%rbx
    4156:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    415a:	e8 91 e2 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    415f:	48 85 c0             	test   %rax,%rax
    4162:	74 6b                	je     41cf <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4164:	4c 89 e7             	mov    %r12,%rdi
    4167:	48 89 c5             	mov    %rax,%rbp
    416a:	31 f6                	xor    %esi,%esi
    416c:	31 c0                	xor    %eax,%eax
    416e:	e8 ed e2 ff ff       	call   2460 <open@plt>
    4173:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4176:	85 c0                	test   %eax,%eax
    4178:	0f 88 b8 e3 ff ff    	js     2536 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    417e:	48 89 da             	mov    %rbx,%rdx
    4181:	48 89 ee             	mov    %rbp,%rsi
    4184:	89 c7                	mov    %eax,%edi
    4186:	e8 e5 e1 ff ff       	call   2370 <read@plt>
    if (ret < file_size) {
    418b:	48 98                	cltq
    418d:	48 39 d8             	cmp    %rbx,%rax
    4190:	7c 1e                	jl     41b0 <copy_file_contents+0x70>
    close(fd);
    4192:	44 89 e7             	mov    %r12d,%edi
    4195:	e8 b6 e1 ff ff       	call   2350 <close@plt>
    iov->iov_base = buf;
    419a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    419e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    41a2:	48 83 c4 08          	add    $0x8,%rsp
    41a6:	5b                   	pop    %rbx
    41a7:	5d                   	pop    %rbp
    41a8:	41 5c                	pop    %r12
    41aa:	41 5d                	pop    %r13
    41ac:	c3                   	ret
    41ad:	0f 1f 00             	nopl   (%rax)
    41b0:	48 8b 0d 69 4e 00 00 	mov    0x4e69(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    41b7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    41bc:	be 01 00 00 00       	mov    $0x1,%esi
    41c1:	48 8d 3d 08 1f 00 00 	lea    0x1f08(%rip),%rdi        # 60d0 <_IO_stdin_used+0xd0>
    41c8:	e8 d3 e2 ff ff       	call   24a0 <fwrite@plt>
    41cd:	eb c3                	jmp    4192 <copy_file_contents+0x52>
    41cf:	48 8b 0d 4a 4e 00 00 	mov    0x4e4a(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    41d6:	ba 28 00 00 00       	mov    $0x28,%edx
    41db:	be 01 00 00 00       	mov    $0x1,%esi
    41e0:	48 8d 3d 39 22 00 00 	lea    0x2239(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    41e7:	e8 b4 e2 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    41ec:	bf 01 00 00 00       	mov    $0x1,%edi
    41f1:	e8 8a e2 ff ff       	call   2480 <exit@plt>
    41f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004200 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4200:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4204:	8b 46 44             	mov    0x44(%rsi),%eax
    4207:	48 89 fa             	mov    %rdi,%rdx
    420a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    420d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4213:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4216:	48 8b 07             	mov    (%rdi),%rax
    4219:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    421c:	f6 c1 02             	test   $0x2,%cl
    421f:	74 00                	je     4221 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4221:	89 f0                	mov    %esi,%eax
    4223:	44 29 c0             	sub    %r8d,%eax
    4226:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4229:	0f 82 13 e3 ff ff    	jb     2542 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    422f:	c1 e9 0a             	shr    $0xa,%ecx
    4232:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4236:	8b 47 44             	mov    0x44(%rdi),%eax
    4239:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    423c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    423f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4242:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4245:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4249:	d3 e0                	shl    %cl,%eax
    424b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    424e:	48 c1 e0 06          	shl    $0x6,%rax
    4252:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4256:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    425c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    425f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4263:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4269:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4271:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4275:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4278:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    427f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4287:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    428b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    428f:	e8 8c e0 ff ff       	call   2320 <io_uring_submit@plt>
}
    4294:	31 c0                	xor    %eax,%eax
    4296:	48 83 c4 08          	add    $0x8,%rsp
    429a:	c3                   	ret
    429b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000042a0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    42a0:	f3 0f 1e fa          	endbr64
    42a4:	41 55                	push   %r13
    42a6:	41 89 fd             	mov    %edi,%r13d
    42a9:	41 54                	push   %r12
    42ab:	55                   	push   %rbp
    42ac:	53                   	push   %rbx
    42ad:	48 89 f3             	mov    %rsi,%rbx
    42b0:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    42b4:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    42b7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    42bd:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    42c0:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    42c3:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    42c5:	f6 c1 02             	test   $0x2,%cl
    42c8:	74 00                	je     42ca <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    42ca:	89 c2                	mov    %eax,%edx
    42cc:	29 f2                	sub    %esi,%edx
    42ce:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    42d1:	0f 82 7b e2 ff ff    	jb     2552 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    42d7:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    42da:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    42dd:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    42e0:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    42e5:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    42e8:	23 6b 58             	and    0x58(%rbx),%ebp
    42eb:	d3 e5                	shl    %cl,%ebp
    42ed:	48 c1 e5 06          	shl    $0x6,%rbp
    42f1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    42f5:	e8 f6 e0 ff ff       	call   23f0 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    42fa:	be 01 00 00 00       	mov    $0x1,%esi
    42ff:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4304:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4307:	e8 74 e0 ff ff       	call   2380 <calloc@plt>
    req->client_socket = client_socket;
    430c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4311:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4315:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4318:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    431d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4322:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    432b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4333:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4337:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    433b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4342:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    434a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    434e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4356:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    435e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4362:	e8 b9 df ff ff       	call   2320 <io_uring_submit@plt>
}
    4367:	48 83 c4 08          	add    $0x8,%rsp
    436b:	31 c0                	xor    %eax,%eax
    436d:	5b                   	pop    %rbx
    436e:	5d                   	pop    %rbp
    436f:	41 5c                	pop    %r12
    4371:	41 5d                	pop    %r13
    4373:	c3                   	ret
    4374:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    437f:	90                   	nop

0000000000004380 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4380:	f3 0f 1e fa          	endbr64
    4384:	41 56                	push   %r14
    4386:	41 89 f6             	mov    %esi,%r14d
    4389:	41 55                	push   %r13
    438b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    438e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4393:	41 54                	push   %r12
    4395:	55                   	push   %rbp
    4396:	48 89 d5             	mov    %rdx,%rbp
    4399:	53                   	push   %rbx
    void *buf = malloc(size);
    439a:	e8 51 e0 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    439f:	48 85 c0             	test   %rax,%rax
    43a2:	0f 84 dd 00 00 00    	je     4485 <_send_static_string_content+0x105>
    43a8:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    43ab:	4c 89 ef             	mov    %r13,%rdi
    43ae:	e8 4d df ff ff       	call   2300 <strlen@plt>
    req->iovec_count = 1;
    43b3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    43ba:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    43be:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    43c1:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    43c4:	e8 27 e0 ff ff       	call   23f0 <malloc@plt>
    43c9:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    43cc:	48 85 c0             	test   %rax,%rax
    43cf:	0f 84 b0 00 00 00    	je     4485 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    43d5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    43d9:	4c 89 e2             	mov    %r12,%rdx
    43dc:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    43df:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    43e3:	e8 d8 df ff ff       	call   23c0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    43e8:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    43eb:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    43f1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    43f4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    43f8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    43fa:	f6 c1 02             	test   $0x2,%cl
    43fd:	0f 85 7d 00 00 00    	jne    4480 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4403:	89 d0                	mov    %edx,%eax
    4405:	29 f0                	sub    %esi,%eax
    4407:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    440a:	0f 82 4c e1 ff ff    	jb     255c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4410:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4413:	8b 45 44             	mov    0x44(%rbp),%eax
    4416:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4419:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    441c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    441f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4422:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4428:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    442c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    442e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4431:	48 89 ef             	mov    %rbp,%rdi
    4434:	48 c1 e0 06          	shl    $0x6,%rax
    4438:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    443c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    443f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4443:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4449:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4451:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4455:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4458:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    445f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4467:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    446b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    446f:	5b                   	pop    %rbx
    4470:	5d                   	pop    %rbp
    4471:	41 5c                	pop    %r12
    4473:	41 5d                	pop    %r13
    4475:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4477:	e9 a4 de ff ff       	jmp    2320 <io_uring_submit@plt>
    447c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4480:	e9 7e ff ff ff       	jmp    4403 <_send_static_string_content+0x83>
    4485:	48 8b 0d 94 4b 00 00 	mov    0x4b94(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    448c:	ba 28 00 00 00       	mov    $0x28,%edx
    4491:	be 01 00 00 00       	mov    $0x1,%esi
    4496:	48 8d 3d 83 1f 00 00 	lea    0x1f83(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    449d:	e8 fe df ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    44a2:	bf 01 00 00 00       	mov    $0x1,%edi
    44a7:	e8 d4 df ff ff       	call   2480 <exit@plt>
    44ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000044b0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    44b0:	f3 0f 1e fa          	endbr64
    44b4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    44b7:	89 fe                	mov    %edi,%esi
    44b9:	48 8b 3d 58 4b 00 00 	mov    0x4b58(%rip),%rdi        # 9018 <unimplemented_content>
    44c0:	e9 bb fe ff ff       	jmp    4380 <_send_static_string_content>
    44c5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000044d0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    44d0:	f3 0f 1e fa          	endbr64
    44d4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    44d7:	89 fe                	mov    %edi,%esi
    44d9:	48 8b 3d 30 4b 00 00 	mov    0x4b30(%rip),%rdi        # 9010 <http_404_content>
    44e0:	e9 9b fe ff ff       	jmp    4380 <_send_static_string_content>
    44e5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000044f0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    44f0:	f3 0f 1e fa          	endbr64
    44f4:	41 56                	push   %r14
    44f6:	41 55                	push   %r13
    44f8:	49 89 d5             	mov    %rdx,%r13
    44fb:	41 54                	push   %r12
    44fd:	41 89 f4             	mov    %esi,%r12d
    4500:	55                   	push   %rbp
    4501:	48 89 fd             	mov    %rdi,%rbp
    4504:	53                   	push   %rbx
    4505:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    450c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4515:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    451d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    451f:	e8 dc dd ff ff       	call   2300 <strlen@plt>
    4524:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4529:	48 89 c3             	mov    %rax,%rbx
    452c:	0f 84 b6 00 00 00    	je     45e8 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4532:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4537:	48 89 ee             	mov    %rbp,%rsi
    453a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    453e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4543:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    454b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4553:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    455e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4566:	e8 35 de ff ff       	call   23a0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    456b:	48 89 e6             	mov    %rsp,%rsi
    456e:	4c 89 f7             	mov    %r14,%rdi
    4571:	e8 3a de ff ff       	call   23b0 <stat@plt>
    4576:	83 f8 ff             	cmp    $0xffffffff,%eax
    4579:	0f 84 d3 00 00 00    	je     4652 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    457f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4583:	25 00 f0 00 00       	and    $0xf000,%eax
    4588:	3d 00 80 00 00       	cmp    $0x8000,%eax
    458d:	0f 84 f5 00 00 00    	je     4688 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4593:	48 8b 3d 76 4a 00 00 	mov    0x4a76(%rip),%rdi        # 9010 <http_404_content>
    459a:	4c 89 ea             	mov    %r13,%rdx
    459d:	44 89 e6             	mov    %r12d,%esi
    45a0:	e8 db fd ff ff       	call   4380 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    45a5:	4c 89 f2             	mov    %r14,%rdx
    45a8:	bf 01 00 00 00       	mov    $0x1,%edi
    45ad:	31 c0                	xor    %eax,%eax
    45af:	48 8d 35 6a 1b 00 00 	lea    0x1b6a(%rip),%rsi        # 6120 <_IO_stdin_used+0x120>
    45b6:	e8 75 de ff ff       	call   2430 <__printf_chk@plt>
}
    45bb:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    45c3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    45cc:	0f 85 20 01 00 00    	jne    46f2 <handle_get_method+0x202>
    45d2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    45d9:	5b                   	pop    %rbx
    45da:	5d                   	pop    %rbp
    45db:	41 5c                	pop    %r12
    45dd:	41 5d                	pop    %r13
    45df:	41 5e                	pop    %r14
    45e1:	c3                   	ret
    45e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    45e8:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    45ed:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    45f5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    45fa:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    45fd:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4605:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4608:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4610:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    461b:	e8 80 dd ff ff       	call   23a0 <__memcpy_chk@plt>
    4620:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4625:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    462a:	48 8d 35 ba 1a 00 00 	lea    0x1aba(%rip),%rsi        # 60eb <_IO_stdin_used+0xeb>
    4631:	48 29 d9             	sub    %rbx,%rcx
    4634:	ba 0b 00 00 00       	mov    $0xb,%edx
    4639:	e8 62 dd ff ff       	call   23a0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    463e:	48 89 e6             	mov    %rsp,%rsi
    4641:	4c 89 f7             	mov    %r14,%rdi
    4644:	e8 67 dd ff ff       	call   23b0 <stat@plt>
    4649:	83 f8 ff             	cmp    $0xffffffff,%eax
    464c:	0f 85 2d ff ff ff    	jne    457f <handle_get_method+0x8f>
    4652:	4c 89 f2             	mov    %r14,%rdx
    4655:	48 89 e9             	mov    %rbp,%rcx
    4658:	48 8d 35 97 1a 00 00 	lea    0x1a97(%rip),%rsi        # 60f6 <_IO_stdin_used+0xf6>
    465f:	31 c0                	xor    %eax,%eax
    4661:	bf 01 00 00 00       	mov    $0x1,%edi
    4666:	e8 c5 dd ff ff       	call   2430 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    466b:	48 8b 3d 9e 49 00 00 	mov    0x499e(%rip),%rdi        # 9010 <http_404_content>
    4672:	4c 89 ea             	mov    %r13,%rdx
    4675:	44 89 e6             	mov    %r12d,%esi
    4678:	e8 03 fd ff ff       	call   4380 <_send_static_string_content>
}
    467d:	e9 39 ff ff ff       	jmp    45bb <handle_get_method+0xcb>
    4682:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4688:	bf 70 00 00 00       	mov    $0x70,%edi
    468d:	e8 5e dd ff ff       	call   23f0 <malloc@plt>
    4692:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4695:	48 85 c0             	test   %rax,%rax
    4698:	74 5d                	je     46f7 <handle_get_method+0x207>
            req->client_socket = client_socket;
    469a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    469e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    46a3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    46a7:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    46aa:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    46b1:	e8 5a f5 ff ff       	call   3c10 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    46b6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    46bb:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    46bf:	4c 89 f7             	mov    %r14,%rdi
    46c2:	e8 79 fa ff ff       	call   4140 <copy_file_contents>
    46c7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    46cc:	4c 89 f2             	mov    %r14,%rdx
    46cf:	31 c0                	xor    %eax,%eax
    46d1:	48 8d 35 36 1a 00 00 	lea    0x1a36(%rip),%rsi        # 610e <_IO_stdin_used+0x10e>
    46d8:	bf 01 00 00 00       	mov    $0x1,%edi
    46dd:	e8 4e dd ff ff       	call   2430 <__printf_chk@plt>
            add_write_request(req, ring);
    46e2:	4c 89 ee             	mov    %r13,%rsi
    46e5:	48 89 df             	mov    %rbx,%rdi
    46e8:	e8 13 fb ff ff       	call   4200 <add_write_request>
    46ed:	e9 c9 fe ff ff       	jmp    45bb <handle_get_method+0xcb>
}
    46f2:	e8 19 dc ff ff       	call   2310 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    46f7:	48 8b 0d 22 49 00 00 	mov    0x4922(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    46fe:	ba 28 00 00 00       	mov    $0x28,%edx
    4703:	be 01 00 00 00       	mov    $0x1,%esi
    4708:	48 8d 3d 11 1d 00 00 	lea    0x1d11(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    470f:	e8 8c dd ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    4714:	bf 01 00 00 00       	mov    $0x1,%edi
    4719:	e8 62 dd ff ff       	call   2480 <exit@plt>
    471e:	66 90                	xchg   %ax,%ax

0000000000004720 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4720:	f3 0f 1e fa          	endbr64
    4724:	41 57                	push   %r15
    4726:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    4728:	4c 8d 35 56 19 00 00 	lea    0x1956(%rip),%r14        # 6085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    472f:	41 55                	push   %r13
    4731:	49 89 d5             	mov    %rdx,%r13
    4734:	41 54                	push   %r12
    4736:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4739:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    473c:	55                   	push   %rbp
    473d:	53                   	push   %rbx
    473e:	48 83 ec 18          	sub    $0x18,%rsp
    4742:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    474b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4750:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4752:	49 89 e7             	mov    %rsp,%r15
    4755:	4c 89 fa             	mov    %r15,%rdx
    4758:	e8 03 dc ff ff       	call   2360 <strtok_r@plt>
    for (; *str; ++str)
    475d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4761:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4764:	84 db                	test   %bl,%bl
    4766:	74 1d                	je     4785 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4768:	e8 83 dd ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    476d:	48 89 ea             	mov    %rbp,%rdx
    4770:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4773:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4777:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    477a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    477d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4781:	84 db                	test   %bl,%bl
    4783:	75 eb                	jne    4770 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4785:	4c 89 fa             	mov    %r15,%rdx
    4788:	4c 89 f6             	mov    %r14,%rsi
    478b:	31 ff                	xor    %edi,%edi
    478d:	e8 ce db ff ff       	call   2360 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4792:	48 8d 35 9a 19 00 00 	lea    0x199a(%rip),%rsi        # 6133 <_IO_stdin_used+0x133>
    4799:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    479c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    479f:	e8 ec db ff ff       	call   2390 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    47a4:	4c 89 ea             	mov    %r13,%rdx
    47a7:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    47aa:	85 c0                	test   %eax,%eax
    47ac:	75 2a                	jne    47d8 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    47ae:	48 89 df             	mov    %rbx,%rdi
    47b1:	e8 3a fd ff ff       	call   44f0 <handle_get_method>
}
    47b6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    47bb:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    47c4:	75 20                	jne    47e6 <handle_http_method+0xc6>
    47c6:	48 83 c4 18          	add    $0x18,%rsp
    47ca:	5b                   	pop    %rbx
    47cb:	5d                   	pop    %rbp
    47cc:	41 5c                	pop    %r12
    47ce:	41 5d                	pop    %r13
    47d0:	41 5e                	pop    %r14
    47d2:	41 5f                	pop    %r15
    47d4:	c3                   	ret
    47d5:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    47d8:	48 8b 3d 39 48 00 00 	mov    0x4839(%rip),%rdi        # 9018 <unimplemented_content>
    47df:	e8 9c fb ff ff       	call   4380 <_send_static_string_content>
}
    47e4:	eb d0                	jmp    47b6 <handle_http_method+0x96>
    47e6:	e8 25 db ff ff       	call   2310 <__stack_chk_fail@plt>
    47eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000047f0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    47f0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    47f4:	85 d2                	test   %edx,%edx
    47f6:	7e 38                	jle    4830 <get_line+0x40>
    47f8:	48 63 d2             	movslq %edx,%rdx
    47fb:	48 83 c7 01          	add    $0x1,%rdi
    47ff:	48 01 f2             	add    %rsi,%rdx
    4802:	eb 11                	jmp    4815 <get_line+0x25>
    4804:	0f 1f 40 00          	nopl   0x0(%rax)
    4808:	48 83 c6 01          	add    $0x1,%rsi
    480c:	48 83 c7 01          	add    $0x1,%rdi
    4810:	48 39 d6             	cmp    %rdx,%rsi
    4813:	74 1b                	je     4830 <get_line+0x40>
        dest[i] = src[i];
    4815:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4819:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    481b:	3c 0d                	cmp    $0xd,%al
    481d:	75 e9                	jne    4808 <get_line+0x18>
    481f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4822:	75 e4                	jne    4808 <get_line+0x18>
            dest[i] = '\0';
    4824:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4827:	31 c0                	xor    %eax,%eax
    4829:	c3                   	ret
    482a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4830:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4835:	c3                   	ret
    4836:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004840 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4840:	f3 0f 1e fa          	endbr64
    4844:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    484b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    484f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4858:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4860:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4862:	49 89 e2             	mov    %rsp,%r10
    4865:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    486d:	4c 89 d0             	mov    %r10,%rax
    4870:	eb 13                	jmp    4885 <handle_client_request+0x45>
    4872:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4878:	48 83 c0 01          	add    $0x1,%rax
    487c:	48 83 c1 01          	add    $0x1,%rcx
    4880:	4c 39 c8             	cmp    %r9,%rax
    4883:	74 4b                	je     48d0 <handle_client_request+0x90>
        dest[i] = src[i];
    4885:	44 0f b6 01          	movzbl (%rcx),%r8d
    4889:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    488c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4890:	75 e6                	jne    4878 <handle_client_request+0x38>
    4892:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4896:	75 e0                	jne    4878 <handle_client_request+0x38>
            dest[i] = '\0';
    4898:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    489b:	8b 47 08             	mov    0x8(%rdi),%eax
    489e:	48 89 f2             	mov    %rsi,%rdx
    48a1:	4c 89 d7             	mov    %r10,%rdi
    48a4:	89 c6                	mov    %eax,%esi
    48a6:	e8 75 fe ff ff       	call   4720 <handle_http_method>
}
    48ab:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    48b3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    48bc:	75 39                	jne    48f7 <handle_client_request+0xb7>
    48be:	31 c0                	xor    %eax,%eax
    48c0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    48c7:	c3                   	ret
    48c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    48d0:	48 8b 0d 49 47 00 00 	mov    0x4749(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    48d7:	ba 12 00 00 00       	mov    $0x12,%edx
    48dc:	be 01 00 00 00       	mov    $0x1,%esi
    48e1:	48 8d 3d 4f 18 00 00 	lea    0x184f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    48e8:	e8 b3 db ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    48ed:	bf 01 00 00 00       	mov    $0x1,%edi
    48f2:	e8 89 db ff ff       	call   2480 <exit@plt>
}
    48f7:	e8 14 da ff ff       	call   2310 <__stack_chk_fail@plt>
    48fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004900 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4900:	f3 0f 1e fa          	endbr64
    4904:	55                   	push   %rbp
    4905:	53                   	push   %rbx
    4906:	48 89 cb             	mov    %rcx,%rbx
    4909:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    490d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4910:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4913:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4919:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    491c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    491f:	f6 c1 02             	test   $0x2,%cl
    4922:	74 00                	je     4924 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4924:	41 89 c0             	mov    %eax,%r8d
    4927:	45 29 c8             	sub    %r9d,%r8d
    492a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    492e:	0f 82 38 dc ff ff    	jb     256c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4934:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4937:	8b 6b 44             	mov    0x44(%rbx),%ebp
    493a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    493d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4940:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4943:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4947:	d3 e5                	shl    %cl,%ebp
    4949:	48 c1 e5 06          	shl    $0x6,%rbp
    494d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4951:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4954:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4959:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4960:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4964:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4968:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4970:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4978:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    497c:	e8 6f da ff ff       	call   23f0 <malloc@plt>
  io_uring_submit(ring);
    4981:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4984:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    498a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    498e:	48 83 c4 08          	add    $0x8,%rsp
    4992:	5b                   	pop    %rbx
    4993:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4994:	e9 87 d9 ff ff       	jmp    2320 <io_uring_submit@plt>
    4999:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000049a0 <io_thread>:
void* io_thread(void *arg) {
    49a0:	f3 0f 1e fa          	endbr64
    49a4:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    49a6:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    49a8:	41 56                	push   %r14
    49aa:	41 55                	push   %r13
    49ac:	41 54                	push   %r12
    49ae:	55                   	push   %rbp
    49af:	48 89 fd             	mov    %rdi,%rbp
    49b2:	53                   	push   %rbx
    49b3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    49ba:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    49c3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    49cb:	48 8b 47 40          	mov    0x40(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    49cf:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    49d4:	bf 00 01 00 00       	mov    $0x100,%edi
    49d9:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    49dc:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    49e0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    49e5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    49ea:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    49ef:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    49f4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    49fc:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4a01:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4a09:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4a0e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4a16:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4a1b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4a23:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4a28:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4a30:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4a35:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4a3d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4a45:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4a4d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4a55:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4a5d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4a65:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4a6d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4a75:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4a7d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4a85:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4a8d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4a94:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4a9c:	e8 2f d9 ff ff       	call   23d0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4aa1:	48 8b 7d 40          	mov    0x40(%rbp),%rdi
    4aa5:	31 f6                	xor    %esi,%esi
    4aa7:	e8 14 da ff ff       	call   24c0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4aac:	31 d2                	xor    %edx,%edx
    4aae:	be 01 00 00 00       	mov    $0x1,%esi
    4ab3:	bf 02 00 00 00       	mov    $0x2,%edi
    4ab8:	e8 53 da ff ff       	call   2510 <socket@plt>
  if (sock == -1)
    4abd:	83 f8 ff             	cmp    $0xffffffff,%eax
    4ac0:	0f 84 e8 da ff ff    	je     25ae <io_thread.cold+0x38>
  if (setsockopt(sock,
    4ac6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4acb:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4ad1:	89 c7                	mov    %eax,%edi
    4ad3:	41 89 c4             	mov    %eax,%r12d
    4ad6:	ba 02 00 00 00       	mov    $0x2,%edx
    4adb:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    4ae0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    4ae8:	e8 f3 d7 ff ff       	call   22e0 <setsockopt@plt>
    4aed:	85 c0                	test   %eax,%eax
    4aef:	0f 88 8d da ff ff    	js     2582 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    4af5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4afa:	ba 10 00 00 00       	mov    $0x10,%edx
    4aff:	44 89 e7             	mov    %r12d,%edi
    4b02:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4b0b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4b13:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    4b1b:	e8 20 d9 ff ff       	call   2440 <bind@plt>
    4b20:	85 c0                	test   %eax,%eax
    4b22:	0f 88 92 da ff ff    	js     25ba <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4b28:	be 0a 00 00 00       	mov    $0xa,%esi
    4b2d:	44 89 e7             	mov    %r12d,%edi
    4b30:	e8 cb d8 ff ff       	call   2400 <listen@plt>
    4b35:	85 c0                	test   %eax,%eax
    4b37:	0f 88 51 da ff ff    	js     258e <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4b3d:	ba db 18 00 00       	mov    $0x18db,%edx
    4b42:	48 8d 35 33 16 00 00 	lea    0x1633(%rip),%rsi        # 617c <_IO_stdin_used+0x17c>
    4b49:	bf 01 00 00 00       	mov    $0x1,%edi
    4b4e:	31 c0                	xor    %eax,%eax
    4b50:	e8 db d8 ff ff       	call   2430 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4b55:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4b5a:	48 89 d9             	mov    %rbx,%rcx
    4b5d:	44 89 e7             	mov    %r12d,%edi
    4b60:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4b65:	48 89 c6             	mov    %rax,%rsi
    4b68:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4b6d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    4b72:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4b7a:	e8 81 fd ff ff       	call   4900 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4b7f:	bf 01 00 00 00       	mov    $0x1,%edi
    4b84:	be 10 00 00 00       	mov    $0x10,%esi
    4b89:	e8 f2 d7 ff ff       	call   2380 <calloc@plt>
    void *buf = malloc(size);
    4b8e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4b93:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    4b96:	e8 55 d8 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    4b9b:	48 85 c0             	test   %rax,%rax
    4b9e:	0f 84 ae 04 00 00    	je     5052 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    4ba4:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4ba8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4baf:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    4bb6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4bbe:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4bc1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4bc6:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4bc8:	f6 c1 02             	test   $0x2,%cl
    4bcb:	0f 85 0f 04 00 00    	jne    4fe0 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    4bd1:	89 d0                	mov    %edx,%eax
    4bd3:	29 f0                	sub    %esi,%eax
    4bd5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4bdc:	0f 82 c2 d9 ff ff    	jb     25a4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    4be2:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4be5:	48 8d 75 48          	lea    0x48(%rbp),%rsi
	sqe->addr3 = 0;
    4be9:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    4bed:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4bf0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4bf7:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4bfa:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4c01:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4c08:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4c0a:	8b 55 48             	mov    0x48(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4c0d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4c12:	48 c1 e0 06          	shl    $0x6,%rax
    4c16:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4c1e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4c24:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4c27:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4c2f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4c33:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4c3b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4c43:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4c47:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    4c4b:	e8 d0 d6 ff ff       	call   2320 <io_uring_submit@plt>
  while (data->running == 1) {
    4c50:	83 7d 2c 01          	cmpl   $0x1,0x2c(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4c54:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4c59:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4c61:	0f 85 d7 01 00 00    	jne    4e3e <io_thread+0x49e>
    4c67:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4c6c:	4d 89 ce             	mov    %r9,%r14
    4c6f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4c74:	0f 1f 40 00          	nopl   0x0(%rax)
    4c78:	48 8d 3d 13 15 00 00 	lea    0x1513(%rip),%rdi        # 6192 <_IO_stdin_used+0x192>
    4c7f:	e8 4c d6 ff ff       	call   22d0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    4c84:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    4c8b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    4c92:	c1 e9 0b             	shr    $0xb,%ecx
    4c95:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    4c98:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4ca0:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    4ca2:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    4caa:	8b 16                	mov    (%rsi),%edx
		if (!available)
    4cac:	39 d0                	cmp    %edx,%eax
    4cae:	74 36                	je     4ce6 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    4cb0:	89 f8                	mov    %edi,%eax
    4cb2:	21 d0                	and    %edx,%eax
    4cb4:	d3 e0                	shl    %cl,%eax
    4cb6:	48 c1 e0 04          	shl    $0x4,%rax
    4cba:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    4cc2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    4cca:	0f 85 a8 01 00 00    	jne    4e78 <io_thread+0x4d8>
    4cd0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4cd4:	0f 85 0e 03 00 00    	jne    4fe8 <io_thread+0x648>
			if (cqe->res < 0)
    4cda:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4cdd:	83 c2 01             	add    $0x1,%edx
    4ce0:	89 16                	mov    %edx,(%rsi)
			if (!err)
    4ce2:	85 c0                	test   %eax,%eax
    4ce4:	79 b2                	jns    4c98 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    4ce6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    4cef:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4cf0:	45 31 c0             	xor    %r8d,%r8d
    4cf3:	31 d2                	xor    %edx,%edx
    4cf5:	b9 01 00 00 00       	mov    $0x1,%ecx
    4cfa:	4c 89 f6             	mov    %r14,%rsi
    4cfd:	48 89 df             	mov    %rbx,%rdi
    4d00:	e8 1b d7 ff ff       	call   2420 <__io_uring_get_cqe@plt>
    4d05:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    4d08:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4d0d:	48 83 38 01          	cmpq   $0x1,(%rax)
    4d11:	0f 84 e1 02 00 00    	je     4ff8 <io_thread+0x658>
    4d17:	48 8d 3d 9a 14 00 00 	lea    0x149a(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4d1e:	e8 ad d5 ff ff       	call   22d0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4d23:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4d28:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    4d2b:	45 85 ff             	test   %r15d,%r15d
    4d2e:	0f 88 42 d8 ff ff    	js     2576 <io_thread.cold>
      if (cqe->res < 0) {
    4d34:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    4d37:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    4d3b:	85 c0                	test   %eax,%eax
    4d3d:	0f 88 d5 02 00 00    	js     5018 <io_thread+0x678>
      switch (req->event_type) {
    4d43:	41 83 f8 01          	cmp    $0x1,%r8d
    4d47:	0f 84 7b 01 00 00    	je     4ec8 <io_thread+0x528>
    4d4d:	41 83 f8 02          	cmp    $0x2,%r8d
    4d51:	0f 84 a1 01 00 00    	je     4ef8 <io_thread+0x558>
    4d57:	45 85 c0             	test   %r8d,%r8d
    4d5a:	0f 85 50 01 00 00    	jne    4eb0 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4d60:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    4d65:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    4d6a:	48 89 d9             	mov    %rbx,%rcx
    4d6d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    4d71:	e8 8a fb ff ff       	call   4900 <add_accept_request>
              add_read_request(cqe->res, &ring);
    4d76:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4d7b:	48 89 de             	mov    %rbx,%rsi
    4d7e:	8b 78 08             	mov    0x8(%rax),%edi
    4d81:	e8 1a f5 ff ff       	call   42a0 <add_read_request>
              free(req);
    4d86:	4c 89 e7             	mov    %r12,%rdi
    4d89:	e8 22 d5 ff ff       	call   22b0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    4d8e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    4d93:	48 85 c0             	test   %rax,%rax
    4d96:	0f 85 14 01 00 00    	jne    4eb0 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    4d9c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4da3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4daa:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4dad:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4db2:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4db4:	f6 c1 02             	test   $0x2,%cl
    4db7:	74 00                	je     4db9 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    4db9:	89 d0                	mov    %edx,%eax
    4dbb:	29 f0                	sub    %esi,%eax
    4dbd:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4dc4:	0f 82 d0 d7 ff ff    	jb     259a <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    4dca:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    4dcd:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    4dd2:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    4dd6:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4dd9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4de0:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4de3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4dea:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4df1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4df3:	8b 55 48             	mov    0x48(%rbp),%edx
    4df6:	48 c1 e0 06          	shl    $0x6,%rax
    4dfa:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4e02:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4e08:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4e0b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4e13:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4e17:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4e1f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4e27:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4e2b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    4e2f:	e8 ec d4 ff ff       	call   2320 <io_uring_submit@plt>
  while (data->running == 1) {
    4e34:	83 7d 2c 01          	cmpl   $0x1,0x2c(%rbp)
    4e38:	0f 84 3a fe ff ff    	je     4c78 <io_thread+0x2d8>
    4e3e:	48 8d 3d ac 13 00 00 	lea    0x13ac(%rip),%rdi        # 61f1 <_IO_stdin_used+0x1f1>
    4e45:	e8 86 d4 ff ff       	call   22d0 <puts@plt>
}
    4e4a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    4e52:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4e5b:	0f 85 18 02 00 00    	jne    5079 <io_thread+0x6d9>
    4e61:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    4e68:	31 c0                	xor    %eax,%eax
    4e6a:	5b                   	pop    %rbx
    4e6b:	5d                   	pop    %rbp
    4e6c:	41 5c                	pop    %r12
    4e6e:	41 5d                	pop    %r13
    4e70:	41 5e                	pop    %r14
    4e72:	41 5f                	pop    %r15
    4e74:	c3                   	ret
    4e75:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    4e78:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    4e7d:	48 85 c0             	test   %rax,%rax
    4e80:	0f 84 6a fe ff ff    	je     4cf0 <io_thread+0x350>
      if (cqe->user_data == 1) {
    4e86:	48 83 38 01          	cmpq   $0x1,(%rax)
    4e8a:	0f 84 68 01 00 00    	je     4ff8 <io_thread+0x658>
    4e90:	48 8d 3d 21 13 00 00 	lea    0x1321(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4e97:	e8 34 d4 ff ff       	call   22d0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4e9c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4ea1:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    4ea4:	e9 8b fe ff ff       	jmp    4d34 <io_thread+0x394>
    4ea9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4eb0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    4eb8:	8b 02                	mov    (%rdx),%eax
    4eba:	83 c0 01             	add    $0x1,%eax
    4ebd:	89 02                	mov    %eax,(%rdx)
}
    4ebf:	e9 d8 fe ff ff       	jmp    4d9c <io_thread+0x3fc>
    4ec4:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    4ec8:	85 c0                	test   %eax,%eax
    4eca:	75 74                	jne    4f40 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4ecc:	48 8b 0d 4d 41 00 00 	mov    0x414d(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4ed3:	ba 0f 00 00 00       	mov    $0xf,%edx
    4ed8:	be 01 00 00 00       	mov    $0x1,%esi
    4edd:	48 8d 3d fd 12 00 00 	lea    0x12fd(%rip),%rdi        # 61e1 <_IO_stdin_used+0x1e1>
    4ee4:	e8 b7 d5 ff ff       	call   24a0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    4ee9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4eee:	e9 a0 fe ff ff       	jmp    4d93 <io_thread+0x3f3>
    4ef3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    4ef8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    4efd:	45 31 ff             	xor    %r15d,%r15d
    4f00:	85 c0                	test   %eax,%eax
    4f02:	7e 20                	jle    4f24 <io_thread+0x584>
    4f04:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    4f08:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    4f0b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    4f0f:	48 c1 e0 04          	shl    $0x4,%rax
    4f13:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    4f18:	e8 93 d3 ff ff       	call   22b0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    4f1d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    4f22:	7f e4                	jg     4f08 <io_thread+0x568>
              close(req->client_socket);
    4f24:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    4f29:	e8 22 d4 ff ff       	call   2350 <close@plt>
              free(req);
    4f2e:	4c 89 e7             	mov    %r12,%rdi
    4f31:	e8 7a d3 ff ff       	call   22b0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    4f36:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    4f3b:	e9 53 fe ff ff       	jmp    4d93 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    4f40:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    4f45:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4f4a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    4f52:	eb 11                	jmp    4f65 <io_thread+0x5c5>
    4f54:	0f 1f 40 00          	nopl   0x0(%rax)
    4f58:	48 83 c0 01          	add    $0x1,%rax
    4f5c:	48 83 c2 01          	add    $0x1,%rdx
    4f60:	48 39 c6             	cmp    %rax,%rsi
    4f63:	74 4b                	je     4fb0 <io_thread+0x610>
        dest[i] = src[i];
    4f65:	0f b6 0a             	movzbl (%rdx),%ecx
    4f68:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    4f6a:	80 f9 0d             	cmp    $0xd,%cl
    4f6d:	75 e9                	jne    4f58 <io_thread+0x5b8>
    4f6f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    4f73:	75 e3                	jne    4f58 <io_thread+0x5b8>
            dest[i] = '\0';
    4f75:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    4f78:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    4f7d:	48 89 da             	mov    %rbx,%rdx
    4f80:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    4f85:	e8 96 f7 ff ff       	call   4720 <handle_http_method>
              free(req->iov[0].iov_base);
    4f8a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    4f8f:	e8 1c d3 ff ff       	call   22b0 <free@plt>
              free(req);
    4f94:	4c 89 e7             	mov    %r12,%rdi
    4f97:	e8 14 d3 ff ff       	call   22b0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    4f9c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    4fa1:	e9 ed fd ff ff       	jmp    4d93 <io_thread+0x3f3>
    4fa6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4fb0:	48 8b 0d 69 40 00 00 	mov    0x4069(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4fb7:	ba 12 00 00 00       	mov    $0x12,%edx
    4fbc:	be 01 00 00 00       	mov    $0x1,%esi
    4fc1:	48 8d 3d 6f 11 00 00 	lea    0x116f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    4fc8:	e8 d3 d4 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    4fcd:	bf 01 00 00 00       	mov    $0x1,%edi
    4fd2:	e8 a9 d4 ff ff       	call   2480 <exit@plt>
    4fd7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    4fe0:	e9 ec fb ff ff       	jmp    4bd1 <io_thread+0x231>
    4fe5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    4fe8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    4fed:	e9 94 fe ff ff       	jmp    4e86 <io_thread+0x4e6>
    4ff2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4ff8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5000:	48 8d 3d 9d 11 00 00 	lea    0x119d(%rip),%rdi        # 61a4 <_IO_stdin_used+0x1a4>
    5007:	8b 02                	mov    (%rdx),%eax
    5009:	83 c0 01             	add    $0x1,%eax
    500c:	89 02                	mov    %eax,(%rdx)
    500e:	e8 bd d2 ff ff       	call   22d0 <puts@plt>
    5013:	e9 26 fe ff ff       	jmp    4e3e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5018:	f7 d8                	neg    %eax
    501a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    501f:	89 c7                	mov    %eax,%edi
    5021:	e8 ba d4 ff ff       	call   24e0 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5026:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    502b:	be 01 00 00 00       	mov    $0x1,%esi
    5030:	48 8b 3d e9 3f 00 00 	mov    0x3fe9(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    5037:	48 89 c1             	mov    %rax,%rcx
    503a:	48 8d 15 0f 14 00 00 	lea    0x140f(%rip),%rdx        # 6450 <_IO_stdin_used+0x450>
    5041:	31 c0                	xor    %eax,%eax
    5043:	e8 68 d4 ff ff       	call   24b0 <__fprintf_chk@plt>
          exit(1);
    5048:	bf 01 00 00 00       	mov    $0x1,%edi
    504d:	e8 2e d4 ff ff       	call   2480 <exit@plt>
    5052:	48 8b 0d c7 3f 00 00 	mov    0x3fc7(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    5059:	ba 28 00 00 00       	mov    $0x28,%edx
    505e:	be 01 00 00 00       	mov    $0x1,%esi
    5063:	48 8d 3d b6 13 00 00 	lea    0x13b6(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    506a:	e8 31 d4 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    506f:	bf 01 00 00 00       	mov    $0x1,%edi
    5074:	e8 07 d4 ff ff       	call   2480 <exit@plt>
}
    5079:	e8 92 d2 ff ff       	call   2310 <__stack_chk_fail@plt>
    507e:	66 90                	xchg   %ax,%ax

0000000000005080 <receive>:
int receive(struct BarrierTask *data) {
    5080:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    5084:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    508a:	85 c0                	test   %eax,%eax
    508c:	0f 8e ea 00 00 00    	jle    517c <receive+0xfc>
int receive(struct BarrierTask *data) {
    5092:	41 54                	push   %r12
    5094:	4c 63 e0             	movslq %eax,%r12
    5097:	48 89 fa             	mov    %rdi,%rdx
    509a:	55                   	push   %rbp
    509b:	49 c1 e4 05          	shl    $0x5,%r12
    509f:	53                   	push   %rbx
    50a0:	48 8b b7 b0 01 00 00 	mov    0x1b0(%rdi),%rsi
    50a7:	49 01 f4             	add    %rsi,%r12
    50aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    50b0:	48 8b 2e             	mov    (%rsi),%rbp
    for (int x = 0 ; x < me->messages_count ; x++) {
    50b3:	48 8b 7d 08          	mov    0x8(%rbp),%rdi
    50b7:	48 85 ff             	test   %rdi,%rdi
    50ba:	0f 8e a0 00 00 00    	jle    5160 <receive+0xe0>
      data->sends++;
    50c0:	48 8b 8a b8 01 00 00 	mov    0x1b8(%rdx),%rcx
    50c7:	4c 8b 45 00          	mov    0x0(%rbp),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    50cb:	4c 63 1a             	movslq (%rdx),%r11
    50ce:	49 89 c9             	mov    %rcx,%r9
    50d1:	48 8d 41 01          	lea    0x1(%rcx),%rax
    50d5:	49 f7 d9             	neg    %r9
    50d8:	48 01 c7             	add    %rax,%rdi
    50db:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    50df:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
      data->mailboxes[n].received++;
    50e6:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    50ea:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    50ed:	49 29 c8             	sub    %rcx,%r8
    50f0:	eb 0f                	jmp    5101 <receive+0x81>
    50f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < me->messages_count ; x++) {
    50f8:	48 83 c0 01          	add    $0x1,%rax
    50fc:	48 39 c7             	cmp    %rax,%rdi
    50ff:	74 5f                	je     5160 <receive+0xe0>
      data->n++;
    5101:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    5105:	48 89 82 b8 01 00 00 	mov    %rax,0x1b8(%rdx)
      data->n++;
    510c:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    5113:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    5117:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    511b:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    5120:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    5124:	75 d2                	jne    50f8 <receive+0x78>
    5126:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    512d:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    5131:	75 c5                	jne    50f8 <receive+0x78>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5133:	bf 01 00 00 00       	mov    $0x1,%edi
    5138:	b9 01 00 00 00       	mov    $0x1,%ecx
    513d:	ba 01 00 00 00       	mov    $0x1,%edx
    5142:	31 c0                	xor    %eax,%eax
    5144:	48 8d 35 2d 13 00 00 	lea    0x132d(%rip),%rsi        # 6478 <_IO_stdin_used+0x478>
    514b:	e8 e0 d2 ff ff       	call   2430 <__printf_chk@plt>
        exit(1);
    5150:	bf 01 00 00 00       	mov    $0x1,%edi
    5155:	e8 26 d3 ff ff       	call   2480 <exit@plt>
    515a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  for (int n = 0 ; n < data->thread_count; n++) {
    5160:	48 83 c6 20          	add    $0x20,%rsi
    me->messages_count = 0;
    5164:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
  for (int n = 0 ; n < data->thread_count; n++) {
    516c:	49 39 f4             	cmp    %rsi,%r12
    516f:	0f 85 3b ff ff ff    	jne    50b0 <receive+0x30>
}
    5175:	5b                   	pop    %rbx
    5176:	31 c0                	xor    %eax,%eax
    5178:	5d                   	pop    %rbp
    5179:	41 5c                	pop    %r12
    517b:	c3                   	ret
    517c:	31 c0                	xor    %eax,%eax
    517e:	c3                   	ret
    517f:	90                   	nop

0000000000005180 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5180:	f3 0f 1e fa          	endbr64
    5184:	41 57                	push   %r15
    5186:	41 56                	push   %r14
    5188:	41 55                	push   %r13
    518a:	41 54                	push   %r12
    518c:	55                   	push   %rbp
    518d:	53                   	push   %rbx
    518e:	48 89 fb             	mov    %rdi,%rbx
    5191:	48 83 ec 28          	sub    $0x28,%rsp
  if (data->thread_index == data->task_index) {
    5195:	8b 07                	mov    (%rdi),%eax
    5197:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    519d:	0f 84 55 01 00 00    	je     52f8 <barriered_work+0x178>
    receive(data);
    51a3:	e8 d8 fe ff ff       	call   5080 <receive>
    while (data->scheduled == 1) {
    51a8:	83 bb 88 01 00 00 01 	cmpl   $0x1,0x188(%rbx)
    51af:	75 1b                	jne    51cc <barriered_work+0x4c>
    51b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    51b8:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    51c0:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    51c3:	83 bb 88 01 00 00 01 	cmpl   $0x1,0x188(%rbx)
    51ca:	74 ec                	je     51b8 <barriered_work+0x38>
    if (data->sending == 1) {
    51cc:	83 bb c0 01 00 00 01 	cmpl   $0x1,0x1c0(%rbx)
    51d3:	74 14                	je     51e9 <barriered_work+0x69>
  asm volatile ("mfence" ::: "memory");
    51d5:	0f ae f0             	mfence
}
    51d8:	48 83 c4 28          	add    $0x28,%rsp
    51dc:	31 c0                	xor    %eax,%eax
    51de:	5b                   	pop    %rbx
    51df:	5d                   	pop    %rbp
    51e0:	41 5c                	pop    %r12
    51e2:	41 5d                	pop    %r13
    51e4:	41 5e                	pop    %r14
    51e6:	41 5f                	pop    %r15
    51e8:	c3                   	ret
        for (int n = 0 ; n < data->thread_count; n++) {
    51e9:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    51ef:	85 c0                	test   %eax,%eax
    51f1:	7e e2                	jle    51d5 <barriered_work+0x55>
          if (n == data->thread_index) { continue; }
    51f3:	8b bb 30 01 00 00    	mov    0x130(%rbx),%edi
    51f9:	4c 63 f8             	movslq %eax,%r15
    51fc:	48 8d 83 c8 01 00 00 	lea    0x1c8(%rbx),%rax
    5203:	31 d2                	xor    %edx,%edx
    5205:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    520a:	48 8d 83 d0 01 00 00 	lea    0x1d0(%rbx),%rax
    5211:	89 7c 24 04          	mov    %edi,0x4(%rsp)
    5215:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    521a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5220:	39 54 24 04          	cmp    %edx,0x4(%rsp)
    5224:	0f 84 b9 00 00 00    	je     52e3 <barriered_work+0x163>
          struct Data *them = data->mailboxes[n].higher;
    522a:	49 89 d0             	mov    %rdx,%r8
    522d:	49 c1 e0 05          	shl    $0x5,%r8
    5231:	4c 03 83 b0 01 00 00 	add    0x1b0(%rbx),%r8
    5238:	4d 8b 48 08          	mov    0x8(%r8),%r9
          for (; them->messages_count < min;) {
    523c:	4d 8b 59 08          	mov    0x8(%r9),%r11
    5240:	49 63 79 10          	movslq 0x10(%r9),%rdi
    5244:	49 39 fb             	cmp    %rdi,%r11
    5247:	0f 8d 96 00 00 00    	jge    52e3 <barriered_work+0x163>
    524d:	49 89 fa             	mov    %rdi,%r10
    5250:	4c 8b b3 08 01 00 00 	mov    0x108(%rbx),%r14
    5257:	49 8b 68 10          	mov    0x10(%r8),%rbp
    525b:	4d 29 da             	sub    %r11,%r10
            them->messages[them->messages_count++] = data->message; 
    525e:	49 8b 09             	mov    (%r9),%rcx
    5261:	49 8d 42 ff          	lea    -0x1(%r10),%rax
    5265:	48 83 f8 02          	cmp    $0x2,%rax
    5269:	0f 86 79 02 00 00    	jbe    54e8 <barriered_work+0x368>
    526f:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5277:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    527f:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5283:	4c 8d 2c 31          	lea    (%rcx,%rsi,1),%r13
    5287:	4c 39 6c 24 08       	cmp    %r13,0x8(%rsp)
    528c:	0f 83 de 01 00 00    	jae    5470 <barriered_work+0x2f0>
    5292:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    5297:	4d 39 ec             	cmp    %r13,%r12
    529a:	0f 83 d0 01 00 00    	jae    5470 <barriered_work+0x2f0>
    52a0:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    52a4:	48 01 ce             	add    %rcx,%rsi
    52a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    52b0:	48 8b 83 c8 01 00 00 	mov    0x1c8(%rbx),%rax
          for (; them->messages_count < min;) {
    52b7:	49 83 c3 08          	add    $0x8,%r11
            them->messages[them->messages_count++] = data->message; 
    52bb:	49 89 43 f8          	mov    %rax,-0x8(%r11)
          for (; them->messages_count < min;) {
    52bf:	4c 39 de             	cmp    %r11,%rsi
    52c2:	75 ec                	jne    52b0 <barriered_work+0x130>
    52c4:	0f 1f 40 00          	nopl   0x0(%rax)
    52c8:	4b 8d 34 16          	lea    (%r14,%r10,1),%rsi
    52cc:	4c 01 d5             	add    %r10,%rbp
    52cf:	48 89 b3 08 01 00 00 	mov    %rsi,0x108(%rbx)
    52d6:	49 89 68 10          	mov    %rbp,0x10(%r8)
    52da:	49 89 79 08          	mov    %rdi,0x8(%r9)
    52de:	48 89 44 f9 f8       	mov    %rax,-0x8(%rcx,%rdi,8)
        for (int n = 0 ; n < data->thread_count; n++) {
    52e3:	48 83 c2 01          	add    $0x1,%rdx
    52e7:	4c 39 fa             	cmp    %r15,%rdx
    52ea:	0f 85 30 ff ff ff    	jne    5220 <barriered_work+0xa0>
    52f0:	e9 e0 fe ff ff       	jmp    51d5 <barriered_work+0x55>
    52f5:	0f 1f 00             	nopl   (%rax)
      receive(data);
    52f8:	e8 83 fd ff ff       	call   5080 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    52fd:	8b 8b 34 01 00 00    	mov    0x134(%rbx),%ecx
        int t = data->task_index;
    5303:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    5305:	85 c9                	test   %ecx,%ecx
    5307:	0f 8e 86 00 00 00    	jle    5393 <barriered_work+0x213>
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    530d:	48 63 e8             	movslq %eax,%rbp
              int next_task = abs((t + 1) % (data->thread_count));
    5310:	83 c0 01             	add    $0x1,%eax
    5313:	4c 63 d9             	movslq %ecx,%r11
    5316:	99                   	cltd
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    5317:	48 c1 e5 09          	shl    $0x9,%rbp
              int next_task = abs((t + 1) % (data->thread_count));
    531b:	f7 f9                	idiv   %ecx
    531d:	89 d0                	mov    %edx,%eax
    531f:	f7 d8                	neg    %eax
    5321:	0f 49 d0             	cmovns %eax,%edx
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    5324:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    532b:	49 c1 e3 05          	shl    $0x5,%r11
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    532f:	31 ff                	xor    %edi,%edi
    5331:	4c 8b 60 10          	mov    0x10(%rax),%r12
              int next_task = abs((t + 1) % (data->thread_count));
    5335:	4c 63 ca             	movslq %edx,%r9
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5338:	49 c1 e1 09          	shl    $0x9,%r9
    533c:	49 83 c4 20          	add    $0x20,%r12
    5340:	4d 89 e2             	mov    %r12,%r10
    5343:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    5348:	49 8b 02             	mov    (%r10),%rax
    534b:	4c 89 e2             	mov    %r12,%rdx
    534e:	48 8b 84 28 b0 01 00 00 	mov    0x1b0(%rax,%rbp,1),%rax
    5356:	4d 8d 04 03          	lea    (%r11,%rax,1),%r8
    535a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5360:	48 8b 0a             	mov    (%rdx),%rcx
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    5363:	48 8b 70 08          	mov    0x8(%rax),%rsi
          for (int b = 0; b < data->thread_count ; b++) {
    5367:	48 83 c0 20          	add    $0x20,%rax
    536b:	48 81 c2 98 00 00 00 	add    $0x98,%rdx
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5372:	4a 8b 8c 09 b0 01 00 00 	mov    0x1b0(%rcx,%r9,1),%rcx
    537a:	48 89 34 39          	mov    %rsi,(%rcx,%rdi,1)
          for (int b = 0; b < data->thread_count ; b++) {
    537e:	49 39 c0             	cmp    %rax,%r8
    5381:	75 dd                	jne    5360 <barriered_work+0x1e0>
        for (int y = 0; y < data->thread_count ; y++) {
    5383:	48 83 c7 20          	add    $0x20,%rdi
    5387:	49 81 c2 98 00 00 00 	add    $0x98,%r10
    538e:	4c 39 df             	cmp    %r11,%rdi
    5391:	75 b5                	jne    5348 <barriered_work+0x1c8>
      asm volatile ("mfence" ::: "memory");
    5393:	0f ae f0             	mfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    5396:	48 8b b3 a0 01 00 00 	mov    0x1a0(%rbx),%rsi
    539d:	31 ff                	xor    %edi,%edi
    539f:	48 c1 e6 05          	shl    $0x5,%rsi
    53a3:	48 03 b3 90 01 00 00 	add    0x190(%rbx),%rsi
    53aa:	e8 41 cf ff ff       	call   22f0 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    53af:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    while (data->scheduled == 1) {
    53b6:	83 bb 88 01 00 00 01 	cmpl   $0x1,0x188(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    53bd:	48 8b 42 30          	mov    0x30(%rdx),%rax
    53c1:	8b 78 10             	mov    0x10(%rax),%edi
    53c4:	8d 6f 01             	lea    0x1(%rdi),%ebp
    53c7:	89 68 10             	mov    %ebp,0x10(%rax)
    while (data->scheduled == 1) {
    53ca:	74 0b                	je     53d7 <barriered_work+0x257>
    53cc:	eb 61                	jmp    542f <barriered_work+0x2af>
    53ce:	66 90                	xchg   %ax,%ax
    if (modcount != data->thread->protected_state->modcount) {
    53d0:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
    53d7:	48 63 83 30 01 00 00 	movslq 0x130(%rbx),%rax
    53de:	48 63 3b             	movslq (%rbx),%rdi
      data->n++;
    53e1:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
    53e9:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    53ed:	48 c1 e7 09          	shl    $0x9,%rdi
    53f1:	48 8d 04 48          	lea    (%rax,%rcx,2),%rax
    53f5:	48 8b 4a 10          	mov    0x10(%rdx),%rcx
    53f9:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    53fd:	48 03 78 20          	add    0x20(%rax),%rdi
    5401:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    5407:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    540a:	83 bb 88 01 00 00 01 	cmpl   $0x1,0x188(%rbx)
    5411:	74 bd                	je     53d0 <barriered_work+0x250>
    if (modcount != data->thread->protected_state->modcount) {
    5413:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    541a:	48 8b 40 30          	mov    0x30(%rax),%rax
    541e:	3b 68 10             	cmp    0x10(%rax),%ebp
    5421:	74 0c                	je     542f <barriered_work+0x2af>
    5423:	48 8d 3d da 0d 00 00 	lea    0xdda(%rip),%rdi        # 6204 <_IO_stdin_used+0x204>
    542a:	e8 a1 ce ff ff       	call   22d0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    542f:	48 8b b3 a0 01 00 00 	mov    0x1a0(%rbx),%rsi
    5436:	31 ff                	xor    %edi,%edi
    5438:	48 c1 e6 05          	shl    $0x5,%rsi
    543c:	48 03 b3 90 01 00 00 	add    0x190(%rbx),%rsi
    5443:	48 83 c6 10          	add    $0x10,%rsi
    5447:	e8 a4 ce ff ff       	call   22f0 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    544c:	48 8b 83 a0 01 00 00 	mov    0x1a0(%rbx),%rax
    5453:	48 83 c0 01          	add    $0x1,%rax
    5457:	48 99                	cqto
    5459:	48 f7 bb 98 01 00 00 	idivq  0x198(%rbx)
    5460:	48 89 93 a0 01 00 00 	mov    %rdx,0x1a0(%rbx)
    5467:	e9 69 fd ff ff       	jmp    51d5 <barriered_work+0x55>
    546c:	0f 1f 40 00          	nopl   0x0(%rax)
    5470:	48 8b 83 c8 01 00 00 	mov    0x1c8(%rbx),%rax
    5477:	4d 89 d5             	mov    %r10,%r13
    547a:	4c 89 e6             	mov    %r12,%rsi
    547d:	49 d1 ed             	shr    %r13
    5480:	49 c1 e5 04          	shl    $0x4,%r13
    5484:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5489:	4c 89 6c 24 18       	mov    %r13,0x18(%rsp)
    548e:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5492:	4d 01 e5             	add    %r12,%r13
    5495:	f6 44 24 18 10       	testb  $0x10,0x18(%rsp)
    549a:	74 14                	je     54b0 <barriered_work+0x330>
            them->messages[them->messages_count++] = data->message; 
    549c:	48 83 c6 10          	add    $0x10,%rsi
    54a0:	41 0f 11 04 24       	movups %xmm0,(%r12)
          for (; them->messages_count < min;) {
    54a5:	49 39 f5             	cmp    %rsi,%r13
    54a8:	74 16                	je     54c0 <barriered_work+0x340>
    54aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
    54b0:	0f 11 06             	movups %xmm0,(%rsi)
    54b3:	48 83 c6 20          	add    $0x20,%rsi
    54b7:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
          for (; them->messages_count < min;) {
    54bb:	49 39 f5             	cmp    %rsi,%r13
    54be:	75 f0                	jne    54b0 <barriered_work+0x330>
    54c0:	4c 89 d6             	mov    %r10,%rsi
    54c3:	48 83 e6 fe          	and    $0xfffffffffffffffe,%rsi
    54c7:	4c 01 de             	add    %r11,%rsi
    54ca:	41 f6 c2 01          	test   $0x1,%r10b
    54ce:	0f 84 f4 fd ff ff    	je     52c8 <barriered_work+0x148>
            them->messages[them->messages_count++] = data->message; 
    54d4:	48 8b 83 c8 01 00 00 	mov    0x1c8(%rbx),%rax
    54db:	48 89 04 f1          	mov    %rax,(%rcx,%rsi,8)
          for (; them->messages_count < min;) {
    54df:	e9 e4 fd ff ff       	jmp    52c8 <barriered_work+0x148>
    54e4:	0f 1f 40 00          	nopl   0x0(%rax)
    54e8:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    54f0:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    54f8:	e9 a3 fd ff ff       	jmp    52a0 <barriered_work+0x120>
    54fd:	0f 1f 00             	nopl   (%rax)

0000000000005500 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5500:	f3 0f 1e fa          	endbr64
    5504:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5508:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    550f:	48 8b 40 38          	mov    0x38(%rax),%rax
    5513:	48 63 10             	movslq (%rax),%rdx
    5516:	85 d2                	test   %edx,%edx
    5518:	7e 2c                	jle    5546 <barriered_work_ingest+0x46>
    551a:	48 8b 40 08          	mov    0x8(%rax),%rax
    551e:	48 c1 e2 04          	shl    $0x4,%rdx
    5522:	48 01 c2             	add    %rax,%rdx
    5525:	0f 1f 00             	nopl   (%rax)
    if (data->thread->buffers->buffer[x].available == 1) {
    5528:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    552c:	75 0f                	jne    553d <barriered_work_ingest+0x3d>
      data->ingest_count++;
    552e:	48 83 87 a8 01 00 00 01 	addq   $0x1,0x1a8(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    5536:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    553d:	48 83 c0 10          	add    $0x10,%rax
    5541:	48 39 d0             	cmp    %rdx,%rax
    5544:	75 e2                	jne    5528 <barriered_work_ingest+0x28>
  asm volatile ("mfence" ::: "memory");
    5546:	0f ae f0             	mfence
  barriered_work(data);
    5549:	e8 32 fc ff ff       	call   5180 <barriered_work>
}
    554e:	31 c0                	xor    %eax,%eax
    5550:	48 83 c4 08          	add    $0x8,%rsp
    5554:	c3                   	ret
    5555:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005560 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5560:	f3 0f 1e fa          	endbr64
}
    5564:	31 c0                	xor    %eax,%eax
    5566:	c3                   	ret
    5567:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005570 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
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
    55de:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    55e3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    55e8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    55ed:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    55f2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    55f7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    55fc:	48 39 fe             	cmp    %rdi,%rsi
    55ff:	7d 2f                	jge    5630 <overlap+0x60>
    5601:	48 39 ca             	cmp    %rcx,%rdx
    5604:	7d 62                	jge    5668 <overlap+0x98>
    5606:	4d 39 da             	cmp    %r11,%r10
    5609:	7d 0e                	jge    5619 <overlap+0x49>
    return 1;
    560b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5610:	4d 39 c1             	cmp    %r8,%r9
    5613:	0f 8c 7f 00 00 00    	jl     5698 <overlap+0xc8>
  return 0;
    5619:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    561b:	4d 39 c1             	cmp    %r8,%r9
    561e:	7f 4c                	jg     566c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5620:	31 c0                	xor    %eax,%eax
    5622:	4d 39 da             	cmp    %r11,%r10
    5625:	0f 9e c0             	setle  %al
    5628:	c3                   	ret
    5629:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5630:	7e 4e                	jle    5680 <overlap+0xb0>
    5632:	48 39 ca             	cmp    %rcx,%rdx
    5635:	7f 39                	jg     5670 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5637:	75 31                	jne    566a <overlap+0x9a>
    5639:	4d 39 c1             	cmp    %r8,%r9
    563c:	7c 2c                	jl     566a <overlap+0x9a>
    return 1;
    563e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5643:	4d 39 da             	cmp    %r11,%r10
    5646:	7d 24                	jge    566c <overlap+0x9c>
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
    5670:	4d 39 da             	cmp    %r11,%r10
    5673:	7e c4                	jle    5639 <overlap+0x69>
    return 1;
    5675:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    567a:	4d 39 c1             	cmp    %r8,%r9
    567d:	7e ba                	jle    5639 <overlap+0x69>
    567f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5680:	48 39 ca             	cmp    %rcx,%rdx
    5683:	7c 94                	jl     5619 <overlap+0x49>
    5685:	4d 39 c1             	cmp    %r8,%r9
    5688:	7d b4                	jge    563e <overlap+0x6e>
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
    56a6:	0f 8e 44 03 00 00    	jle    59f0 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    56ac:	41 57                	push   %r15
    56ae:	41 89 f7             	mov    %esi,%r15d
    56b1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    56b3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    56b6:	41 55                	push   %r13
    56b8:	41 54                	push   %r12
    56ba:	55                   	push   %rbp
    56bb:	53                   	push   %rbx
    56bc:	48 8d 5f 20          	lea    0x20(%rdi),%rbx
    56c0:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    56c4:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    56c9:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    56ce:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    56d1:	45 39 e6             	cmp    %r12d,%r14d
    56d4:	0f 84 4e 02 00 00    	je     5928 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    56da:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    56df:	8b 50 08             	mov    0x8(%rax),%edx
    56e2:	85 d2                	test   %edx,%edx
    56e4:	0f 8e 3e 02 00 00    	jle    5928 <verify+0x288>
    56ea:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    56ef:	31 c9                	xor    %ecx,%ecx
    56f1:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    56f6:	31 c0                	xor    %eax,%eax
    56f8:	44 89 f2             	mov    %r14d,%edx
    56fb:	bf 01 00 00 00       	mov    $0x1,%edi
    5700:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    5705:	48 8d 35 08 0b 00 00 	lea    0xb08(%rip),%rsi        # 6214 <_IO_stdin_used+0x214>
    570c:	e8 1f cd ff ff       	call   2430 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5711:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5716:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    571b:	8b 40 08             	mov    0x8(%rax),%eax
    571e:	85 c0                	test   %eax,%eax
    5720:	0f 8e e6 01 00 00    	jle    590c <verify+0x26c>
    5726:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    5729:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    572e:	31 db                	xor    %ebx,%ebx
    5730:	48 c1 e0 09          	shl    $0x9,%rax
    5734:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    5739:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    573e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5743:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    5748:	4c 8b 20             	mov    (%rax),%r12
    574b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5750:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    5755:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    575a:	49 89 de             	mov    %rbx,%r14
    575d:	48 8d 35 c5 0a 00 00 	lea    0xac5(%rip),%rsi        # 6229 <_IO_stdin_used+0x229>
    5764:	49 c1 e6 09          	shl    $0x9,%r14
    5768:	bf 01 00 00 00       	mov    $0x1,%edi
    576d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5771:	4b 8b 8c 3c a0 01 00 00 	mov    0x1a0(%r12,%r15,1),%rcx
    5779:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    577e:	4a 8b 94 30 a0 01 00 00 	mov    0x1a0(%rax,%r14,1),%rdx
    5786:	31 c0                	xor    %eax,%eax
    5788:	e8 a3 cc ff ff       	call   2430 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    578d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5792:	4c 8b 20             	mov    (%rax),%r12
    5795:	4b 83 bc 3c a0 01 00 00 00 	cmpq   $0x0,0x1a0(%r12,%r15,1)
    579e:	0f 8e 47 01 00 00    	jle    58eb <verify+0x24b>
    57a4:	4c 03 75 00          	add    0x0(%rbp),%r14
    57a8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    57ad:	ba 01 00 00 00       	mov    $0x1,%edx
    57b2:	4d 89 f5             	mov    %r14,%r13
    57b5:	4d 8b b5 a0 01 00 00 	mov    0x1a0(%r13),%r14
    57bc:	4d 85 f6             	test   %r14,%r14
    57bf:	0f 8e 21 01 00 00    	jle    58e6 <verify+0x246>
    57c5:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    57c8:	48 89 d5             	mov    %rdx,%rbp
    57cb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    57d0:	31 db                	xor    %ebx,%ebx
    57d2:	4d 89 f2             	mov    %r14,%r10
    57d5:	48 c1 e5 05          	shl    $0x5,%rbp
    57d9:	48 83 ed 20          	sub    $0x20,%rbp
    57dd:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    57e1:	49 89 ee             	mov    %rbp,%r14
    57e4:	48 89 dd             	mov    %rbx,%rbp
    57e7:	48 89 d3             	mov    %rdx,%rbx
    57ea:	eb 31                	jmp    581d <verify+0x17d>
    57ec:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    57f0:	4c 39 c2             	cmp    %r8,%rdx
    57f3:	0f 8d 57 01 00 00    	jge    5950 <verify+0x2b0>
    57f9:	4c 39 df             	cmp    %r11,%rdi
    57fc:	7e 05                	jle    5803 <verify+0x163>
    57fe:	49 39 c1             	cmp    %rax,%r9
    5801:	7c 75                	jl     5878 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5803:	4c 39 df             	cmp    %r11,%rdi
    5806:	0f 8d ab 01 00 00    	jge    59b7 <verify+0x317>
    580c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5810:	48 83 c5 01          	add    $0x1,%rbp
    5814:	49 39 ea             	cmp    %rbp,%r10
    5817:	0f 8e a9 00 00 00    	jle    58c6 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    581d:	49 8b 97 90 01 00 00 	mov    0x190(%r15),%rdx
    5824:	48 89 e8             	mov    %rbp,%rax
    5827:	48 c1 e0 05          	shl    $0x5,%rax
    582b:	49 03 85 90 01 00 00 	add    0x190(%r13),%rax
    5832:	4c 01 f2             	add    %r14,%rdx
    5835:	48 8b 08             	mov    (%rax),%rcx
    5838:	48 8b 78 10          	mov    0x10(%rax),%rdi
    583c:	48 8b 32             	mov    (%rdx),%rsi
    583f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    5843:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    5847:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    584b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    584f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    5853:	48 39 f1             	cmp    %rsi,%rcx
    5856:	7c 98                	jl     57f0 <verify+0x150>
    5858:	0f 8e 42 01 00 00    	jle    59a0 <verify+0x300>
    585e:	4c 39 c2             	cmp    %r8,%rdx
    5861:	0f 8f f9 00 00 00    	jg     5960 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5867:	75 a7                	jne    5810 <verify+0x170>
    5869:	4c 39 df             	cmp    %r11,%rdi
    586c:	7f a2                	jg     5810 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    586e:	49 39 c1             	cmp    %rax,%r9
    5871:	7c 9d                	jl     5810 <verify+0x170>
    5873:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5878:	49 89 c1             	mov    %rax,%r9
    587b:	48 89 f9             	mov    %rdi,%rcx
    587e:	48 89 f2             	mov    %rsi,%rdx
    5881:	bf 01 00 00 00       	mov    $0x1,%edi
    5886:	48 8d 35 13 0c 00 00 	lea    0xc13(%rip),%rsi        # 64a0 <_IO_stdin_used+0x4a0>
    588d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    588f:	48 83 c5 01          	add    $0x1,%rbp
    5893:	e8 98 cb ff ff       	call   2430 <__printf_chk@plt>
    5898:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    589d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    58a2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    58a5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    58aa:	4d 8b 95 a0 01 00 00 	mov    0x1a0(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    58b1:	4c 8b 20             	mov    (%rax),%r12
    58b4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    58b9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    58bd:	49 39 ea             	cmp    %rbp,%r10
    58c0:	0f 8f 57 ff ff ff    	jg     581d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    58c6:	48 89 da             	mov    %rbx,%rdx
    58c9:	49 3b 9f a0 01 00 00 	cmp    0x1a0(%r15),%rbx
    58d0:	7d 14                	jge    58e6 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    58d2:	4d 8b b5 a0 01 00 00 	mov    0x1a0(%r13),%r14
    58d9:	48 83 c2 01          	add    $0x1,%rdx
    58dd:	4d 85 f6             	test   %r14,%r14
    58e0:	0f 8f e2 fe ff ff    	jg     57c8 <verify+0x128>
    58e6:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    58eb:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    58f0:	48 83 c3 01          	add    $0x1,%rbx
    58f4:	39 58 08             	cmp    %ebx,0x8(%rax)
    58f7:	0f 8f 53 fe ff ff    	jg     5750 <verify+0xb0>
    58fd:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    5902:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    5907:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    590c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5911:	48 83 c1 01          	add    $0x1,%rcx
    5915:	39 48 08             	cmp    %ecx,0x8(%rax)
    5918:	0f 8f d8 fd ff ff    	jg     56f6 <verify+0x56>
    591e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    5923:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    5928:	48 81 44 24 10 98 00 00 00 	addq   $0x98,0x10(%rsp)
    5931:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    5936:	41 39 c7             	cmp    %eax,%r15d
    5939:	0f 84 86 00 00 00    	je     59c5 <verify+0x325>
    593f:	41 89 c4             	mov    %eax,%r12d
    5942:	e9 8a fd ff ff       	jmp    56d1 <verify+0x31>
    5947:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5950:	0f 85 ba fe ff ff    	jne    5810 <verify+0x170>
    5956:	e9 a8 fe ff ff       	jmp    5803 <verify+0x163>
    595b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5960:	49 39 c1             	cmp    %rax,%r9
    5963:	7e 09                	jle    596e <verify+0x2ce>
    5965:	4c 39 df             	cmp    %r11,%rdi
    5968:	0f 8c 0a ff ff ff    	jl     5878 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    596e:	4c 39 df             	cmp    %r11,%rdi
    5971:	0f 8f 99 fe ff ff    	jg     5810 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5977:	49 39 c1             	cmp    %rax,%r9
    597a:	0f 8d f8 fe ff ff    	jge    5878 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5980:	48 39 f1             	cmp    %rsi,%rcx
    5983:	0f 85 87 fe ff ff    	jne    5810 <verify+0x170>
    5989:	4c 39 c2             	cmp    %r8,%rdx
    598c:	0f 85 7e fe ff ff    	jne    5810 <verify+0x170>
    5992:	4c 39 df             	cmp    %r11,%rdi
    5995:	0f 84 dd fe ff ff    	je     5878 <verify+0x1d8>
    599b:	e9 70 fe ff ff       	jmp    5810 <verify+0x170>
    59a0:	4c 39 c2             	cmp    %r8,%rdx
    59a3:	0f 8c 5a fe ff ff    	jl     5803 <verify+0x163>
    59a9:	4c 39 df             	cmp    %r11,%rdi
    59ac:	7e c9                	jle    5977 <verify+0x2d7>
    59ae:	4c 39 c2             	cmp    %r8,%rdx
    59b1:	0f 85 59 fe ff ff    	jne    5810 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    59b7:	49 39 c1             	cmp    %rax,%r9
    59ba:	0f 8f 50 fe ff ff    	jg     5810 <verify+0x170>
    59c0:	e9 b3 fe ff ff       	jmp    5878 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    59c5:	48 81 44 24 18 98 00 00 00 	addq   $0x98,0x18(%rsp)
    59ce:	41 8d 46 01          	lea    0x1(%r14),%eax
    59d2:	45 39 e6             	cmp    %r12d,%r14d
    59d5:	74 08                	je     59df <verify+0x33f>
    59d7:	41 89 c6             	mov    %eax,%r14d
    59da:	e9 ea fc ff ff       	jmp    56c9 <verify+0x29>
}
    59df:	48 83 c4 58          	add    $0x58,%rsp
    59e3:	31 c0                	xor    %eax,%eax
    59e5:	5b                   	pop    %rbx
    59e6:	5d                   	pop    %rbp
    59e7:	41 5c                	pop    %r12
    59e9:	41 5d                	pop    %r13
    59eb:	41 5e                	pop    %r14
    59ed:	41 5f                	pop    %r15
    59ef:	c3                   	ret
    59f0:	31 c0                	xor    %eax,%eax
    59f2:	c3                   	ret

Disassembly of section .fini:

00000000000059f4 <_fini>:
    59f4:	f3 0f 1e fa          	endbr64
    59f8:	48 83 ec 08          	sub    $0x8,%rsp
    59fc:	48 83 c4 08          	add    $0x8,%rsp
    5a00:	c3                   	ret
