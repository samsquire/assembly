
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
    2707:	be 98 00 00 00       	mov    $0x98,%esi
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
    272f:	be 10 00 00 00       	mov    $0x10,%esi
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
    275f:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    2766:	4d 89 c7             	mov    %r8,%r15
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
          } else {
            thread_data[x].tasks[y].run = barriered_work; 
    2769:	4c 89 44 24 48       	mov    %r8,0x48(%rsp)
    276e:	66 90                	xchg   %ax,%ax
    thread_data[x].threads = thread_data;
    2770:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    thread_data[x].thread_index = x;
    2775:	41 89 17             	mov    %edx,(%r15)
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
    2797:	89 54 24 08          	mov    %edx,0x8(%rsp)
    279b:	49 89 47 18          	mov    %rax,0x18(%r15)
    thread_data[x].protected_state = protected_state;
    279f:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    thread_data[x].thread_index = x;
    27a4:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    thread_data[x].protected_state = protected_state;
    27a9:	49 89 47 30          	mov    %rax,0x30(%r15)
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    27ad:	e8 ce fb ff ff       	call   2380 <calloc@plt>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    27b2:	be 10 00 00 00       	mov    $0x10,%esi
    27b7:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    27bc:	49 89 47 50          	mov    %rax,0x50(%r15)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    27c0:	e8 bb fb ff ff       	call   2380 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    27c5:	be 28 00 00 00       	mov    $0x28,%esi
    27ca:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    27cf:	66 0f 6f 15 f9 41 00 00 	movdqa 0x41f9(%rip),%xmm2        # 69d0 <_IO_stdin_used+0x9d0>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    27d7:	49 89 47 58          	mov    %rax,0x58(%r15)
    thread_data[x].timestamp_count = 0;
    27db:	41 0f 11 57 68       	movups %xmm2,0x68(%r15)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    27e0:	e8 9b fb ff ff       	call   2380 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    27e5:	be 80 02 00 00       	mov    $0x280,%esi
    27ea:	bf 07 00 00 00       	mov    $0x7,%edi
    thread_data[x].task_timestamp_count = 0;
    27ef:	66 0f 6f 1d d9 41 00 00 	movdqa 0x41d9(%rip),%xmm3        # 69d0 <_IO_stdin_used+0x9d0>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    27f7:	49 89 47 78          	mov    %rax,0x78(%r15)
    thread_data[x].task_timestamp_count = 0;
    27fb:	41 0f 11 9f 80 00 00 00 	movups %xmm3,0x80(%r15)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2803:	e8 78 fb ff ff       	call   2380 <calloc@plt>
        thread_data[x].tasks[y].sending = 1;
    2808:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    280d:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
      thread_data[x].tasks = barriers;
    2812:	49 89 47 20          	mov    %rax,0x20(%r15)
        thread_data[x].tasks[y].sending = 1;
    2816:	49 89 c7             	mov    %rax,%r15
    2819:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            thread_data[x].tasks[y].protected = do_protected_write; 
    2820:	4c 63 eb             	movslq %ebx,%r13
    2823:	44 89 74 24 28       	mov    %r14d,0x28(%rsp)
    2828:	4f 8d 64 ad 00       	lea    0x0(%r13,%r13,4),%r12
    282d:	49 c1 e4 07          	shl    $0x7,%r12
        if (x == y) {
    2831:	44 39 f3             	cmp    %r14d,%ebx
    2834:	0f 84 f6 09 00 00    	je     3230 <main+0xc60>
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    283a:	be 20 00 00 00       	mov    $0x20,%esi
    283f:	bf 06 00 00 00       	mov    $0x6,%edi
    2844:	e8 37 fb ff ff       	call   2380 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    2849:	89 5c 24 18          	mov    %ebx,0x18(%rsp)
    284d:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
    2852:	48 8d a8 c0 00 00 00 	lea    0xc0(%rax),%rbp
    2859:	4b 89 84 27 28 02 00 00 	mov    %rax,0x228(%r15,%r12,1)
        for (int b = 0 ; b < thread_count ; b++) {
    2861:	49 89 c7             	mov    %rax,%r15
    2864:	0f 1f 40 00          	nopl   0x0(%rax)
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2868:	be 08 00 00 00       	mov    $0x8,%esi
    286d:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < thread_count ; b++) {
    2872:	49 83 c7 20          	add    $0x20,%r15
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2876:	e8 05 fb ff ff       	call   2380 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    287b:	be 08 00 00 00       	mov    $0x8,%esi
    2880:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2885:	49 89 c4             	mov    %rax,%r12
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2888:	e8 f3 fa ff ff       	call   2380 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    288d:	be 00 01 00 00       	mov    $0x100,%esi
    2892:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2897:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    289a:	e8 e1 fa ff ff       	call   2380 <calloc@plt>
          data[0].messages_count = 0;
    289f:	66 0f 6f 05 39 41 00 00 	movdqa 0x4139(%rip),%xmm0        # 69e0 <_IO_stdin_used+0x9e0>
          mailboxes[b].higher = &data[1];
    28a7:	48 8d b0 00 01 00 00 	lea    0x100(%rax),%rsi
          mailboxes[b].lower = &data[0];
    28ae:	49 89 47 e0          	mov    %rax,-0x20(%r15)
          mailboxes[b].higher = &data[1];
    28b2:	49 89 77 e8          	mov    %rsi,-0x18(%r15)
          data[0].messages = messages;
    28b6:	4c 89 20             	mov    %r12,(%rax)
          data[1].messages = messages2;
    28b9:	48 89 98 00 01 00 00 	mov    %rbx,0x100(%rax)
          data[0].messages_count = 0;
    28c0:	0f 29 80 80 00 00 00 	movaps %xmm0,0x80(%rax)
          data[1].messages_count = 0;
    28c7:	0f 29 80 80 01 00 00 	movaps %xmm0,0x180(%rax)
        for (int b = 0 ; b < thread_count ; b++) {
    28ce:	4c 39 fd             	cmp    %r15,%rbp
    28d1:	75 95                	jne    2868 <main+0x298>
        char *message = malloc(sizeof(char) * 256);
    28d3:	be 01 00 00 00       	mov    $0x1,%esi
    28d8:	bf 00 01 00 00       	mov    $0x100,%edi
    28dd:	8b 5c 24 18          	mov    0x18(%rsp),%ebx
    28e1:	4c 8b 64 24 20       	mov    0x20(%rsp),%r12
    28e6:	e8 95 fa ff ff       	call   2380 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    28eb:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    28f0:	48 89 c5             	mov    %rax,%rbp
        struct Message *messaged = malloc(sizeof(struct Message));
    28f3:	e8 f8 fa ff ff       	call   23f0 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    28f8:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    28fd:	48 89 ef             	mov    %rbp,%rdi
    2900:	41 89 d9             	mov    %ebx,%r9d
    2903:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2908:	48 8d 0d 71 3c 00 00 	lea    0x3c71(%rip),%rcx        # 6580 <_IO_stdin_used+0x580>
    290f:	ba 00 01 00 00       	mov    $0x100,%edx
    2914:	31 c0                	xor    %eax,%eax
    2916:	be 01 00 00 00       	mov    $0x1,%esi
    291b:	e8 e0 fb ff ff       	call   2500 <__sprintf_chk@plt>
        messaged->message = message;
    2920:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2925:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    292a:	ba ab aa aa aa       	mov    $0xaaaaaaab,%edx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    292f:	be 20 00 00 00       	mov    $0x20,%esi
    2934:	bf 3f 42 0f 00       	mov    $0xf423f,%edi
        messaged->task_index = y;
    2939:	4d 89 6a 10          	mov    %r13,0x10(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    293d:	44 8d 6b 01          	lea    0x1(%rbx),%r13d
    2941:	4c 8b 78 20          	mov    0x20(%rax),%r15
    2945:	44 89 e8             	mov    %r13d,%eax
    2948:	44 89 e9             	mov    %r13d,%ecx
        messaged->message = message;
    294b:	49 89 2a             	mov    %rbp,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    294e:	48 0f af c2          	imul   %rdx,%rax
    2952:	4b 8d 2c 27          	lea    (%r15,%r12,1),%rbp
        messaged->thread_index = x;
    2956:	4d 89 72 08          	mov    %r14,0x8(%r10)
        thread_data[x].tasks[y].message = messaged;
    295a:	4c 89 95 40 02 00 00 	mov    %r10,0x240(%rbp)
        thread_data[x].tasks[y].snapshot_count = 999999;
    2961:	48 c7 85 10 02 00 00 3f 42 0f 00 	movq   $0xf423f,0x210(%rbp)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    296c:	48 c1 e8 22          	shr    $0x22,%rax
    2970:	8d 04 40             	lea    (%rax,%rax,2),%eax
    2973:	01 c0                	add    %eax,%eax
    2975:	29 c1                	sub    %eax,%ecx
    2977:	89 8d 48 02 00 00    	mov    %ecx,0x248(%rbp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    297d:	e8 fe f9 ff ff       	call   2380 <calloc@plt>
        thread_data[x].tasks[y].thread_index = x;
    2982:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
        thread_data[x].tasks[y].task_index = y;
    2986:	89 5d 00             	mov    %ebx,0x0(%rbp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2989:	48 89 85 08 02 00 00 	mov    %rax,0x208(%rbp)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    2990:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    2995:	48 c7 85 18 02 00 00 00 00 00 00 	movq   $0x0,0x218(%rbp)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    29a0:	48 89 85 28 01 00 00 	mov    %rax,0x128(%rbp)
        thread_data[x].tasks[y].available = 1;
    29a7:	48 8b 05 4a 40 00 00 	mov    0x404a(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
        thread_data[x].tasks[y].thread_index = x;
    29ae:	89 8d 30 01 00 00    	mov    %ecx,0x130(%rbp)
        thread_data[x].tasks[y].available = 1;
    29b4:	48 89 85 80 01 00 00 	mov    %rax,0x180(%rbp)
        thread_data[x].tasks[y].sending = 1;
    29bb:	48 b8 01 00 00 00 06 00 00 00 	movabs $0x600000001,%rax
        thread_data[x].tasks[y].arrived = 0;
    29c5:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        thread_data[x].tasks[y].thread_count = thread_count;
    29cf:	c7 85 34 01 00 00 06 00 00 00 	movl   $0x6,0x134(%rbp)
        thread_data[x].tasks[y].sending = 1;
    29d9:	48 89 85 38 02 00 00 	mov    %rax,0x238(%rbp)
        if (y == barrier_count - 1) {
    29e0:	83 fb 05             	cmp    $0x5,%ebx
    29e3:	0f 84 27 08 00 00    	je     3210 <main+0xc40>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    29e9:	8b 44 24 28          	mov    0x28(%rsp),%eax
    29ed:	39 c3                	cmp    %eax,%ebx
    29ef:	75 67                	jne    2a58 <main+0x488>
    29f1:	8b 5c 24 34          	mov    0x34(%rsp),%ebx
    29f5:	85 db                	test   %ebx,%ebx
    29f7:	7f 5f                	jg     2a58 <main+0x488>
    29f9:	89 ca                	mov    %ecx,%edx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    29fb:	bf 01 00 00 00       	mov    $0x1,%edi
    2a00:	48 8d 35 a1 3b 00 00 	lea    0x3ba1(%rip),%rsi        # 65a8 <_IO_stdin_used+0x5a8>
    2a07:	31 c0                	xor    %eax,%eax
    2a09:	e8 22 fa ff ff       	call   2430 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a0e:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    2a13:	48 63 c3             	movslq %ebx,%rax
    2a16:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    2a1b:	48 89 c1             	mov    %rax,%rcx
    2a1e:	48 c1 e0 04          	shl    $0x4,%rax
    2a22:	48 01 f8             	add    %rdi,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2a25:	4c 8b 7a 20          	mov    0x20(%rdx),%r15
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a29:	48 89 42 38          	mov    %rax,0x38(%rdx)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2a2d:	48 8d 05 ac 2b 00 00 	lea    0x2bac(%rip),%rax        # 55e0 <barriered_work_ingest>
    2a34:	4b 89 84 27 18 01 00 00 	mov    %rax,0x118(%r15,%r12,1)
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a3c:	8d 41 01             	lea    0x1(%rcx),%eax
    2a3f:	89 44 24 34          	mov    %eax,0x34(%rsp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2a43:	41 83 fd 07          	cmp    $0x7,%r13d
    2a47:	74 23                	je     2a6c <main+0x49c>
  int external_thread_index = 0;
    2a49:	44 89 eb             	mov    %r13d,%ebx
    2a4c:	e9 cf fd ff ff       	jmp    2820 <main+0x250>
    2a51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            thread_data[x].tasks[y].run = barriered_work; 
    2a58:	48 8d 05 f1 27 00 00 	lea    0x27f1(%rip),%rax        # 5250 <barriered_work>
    2a5f:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2a66:	41 83 fd 07          	cmp    $0x7,%r13d
    2a6a:	75 dd                	jne    2a49 <main+0x479>

          }
        }
      }
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2a6c:	4c 89 f2             	mov    %r14,%rdx
    2a6f:	48 8d 05 0a 09 00 00 	lea    0x90a(%rip),%rax        # 3380 <barriered_reset>
    2a76:	4d 89 fe             	mov    %r15,%r14
    2a79:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    2a7e:	49 89 86 18 10 00 00 	mov    %rax,0x1018(%r14)
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = thread_count; 
      thread_data[x].tasks[barrier_count].thread_index = x; 
    2a85:	8b 44 24 08          	mov    0x8(%rsp),%eax
  for (int x = 0 ; x < total_threads ; x++) {
    2a89:	48 83 c2 01          	add    $0x1,%rdx
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2a8d:	4d 89 be 28 10 00 00 	mov    %r15,0x1028(%r14)
  for (int x = 0 ; x < total_threads ; x++) {
    2a94:	49 81 c7 98 00 00 00 	add    $0x98,%r15
      thread_data[x].tasks[barrier_count].thread_index = x; 
    2a9b:	41 89 86 30 10 00 00 	mov    %eax,0x1030(%r14)
      thread_data[x].tasks[barrier_count].available = 1; 
    2aa2:	48 8b 05 4f 3f 00 00 	mov    0x3f4f(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2aa9:	41 c7 86 80 0f 00 00 00 00 00 00 	movl   $0x0,0xf80(%r14)
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2ab4:	41 c7 86 00 0f 00 00 06 00 00 00 	movl   $0x6,0xf00(%r14)
      thread_data[x].tasks[barrier_count].thread_count = thread_count; 
    2abf:	41 c7 86 34 10 00 00 06 00 00 00 	movl   $0x6,0x1034(%r14)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2aca:	41 c7 86 3c 11 00 00 06 00 00 00 	movl   $0x6,0x113c(%r14)
      thread_data[x].tasks[barrier_count].available = 1; 
    2ad5:	49 89 86 80 10 00 00 	mov    %rax,0x1080(%r14)
  for (int x = 0 ; x < total_threads ; x++) {
    2adc:	48 83 fa 09          	cmp    $0x9,%rdx
    2ae0:	0f 85 8a fc ff ff    	jne    2770 <main+0x1a0>
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].threads = thread_data;
    2ae6:	4c 8b 44 24 48       	mov    0x48(%rsp),%r8
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2aeb:	be 38 00 00 00       	mov    $0x38,%esi
    2af0:	bf 09 00 00 00       	mov    $0x9,%edi
  thread_data[thread_count].thread_count = thread_count;
  thread_data[thread_count].thread_index = 0;

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
  for (int x = 0 ; x < thread_count ; x++) {
    2af5:	45 31 ed             	xor    %r13d,%r13d
    2af8:	4c 8d 3d 11 09 00 00 	lea    0x911(%rip),%r15        # 3410 <barriered_thread>
    thread_data[n].tasks[0].scheduled = 1;
    2aff:	49 8b 40 20          	mov    0x20(%r8),%rax
    2b03:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    thread_data[x].threads = thread_data;
    2b08:	4d 89 80 38 04 00 00 	mov    %r8,0x438(%r8)
    thread_data[x].thread_count = thread_count;
    2b0f:	41 c7 80 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r8)
    thread_data[x].thread_index = x;
    2b1a:	41 c7 80 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r8)
    thread_data[x].task_count = total_barrier_count;
    2b25:	41 c7 80 50 04 00 00 07 00 00 00 	movl   $0x7,0x450(%r8)
    thread_data[n].tasks[0].scheduled = 1;
    2b30:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
    2b3a:	49 8b 80 b8 00 00 00 	mov    0xb8(%r8),%rax
    2b41:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
    2b4b:	49 8b 80 50 01 00 00 	mov    0x150(%r8),%rax
    2b52:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
    2b5c:	49 8b 80 e8 01 00 00 	mov    0x1e8(%r8),%rax
    2b63:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
    2b6d:	49 8b 80 80 02 00 00 	mov    0x280(%r8),%rax
    2b74:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
    2b7e:	49 8b 80 18 03 00 00 	mov    0x318(%r8),%rax
    2b85:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b8f:	e8 ec f7 ff ff       	call   2380 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b94:	be 38 00 00 00       	mov    $0x38,%esi
    2b99:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b9e:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ba1:	e8 da f7 ff ff       	call   2380 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2ba6:	be 38 00 00 00       	mov    $0x38,%esi
    2bab:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bb0:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bb5:	e8 c6 f7 ff ff       	call   2380 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2bba:	be 08 00 00 00       	mov    $0x8,%esi
    2bbf:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bc4:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2bc9:	e8 b2 f7 ff ff       	call   2380 <calloc@plt>
  thread_data[thread_count].task_count = total_barrier_count;
    2bce:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2bd3:	ba 06 00 00 00       	mov    $0x6,%edx
    2bd8:	48 8d 35 10 37 00 00 	lea    0x3710(%rip),%rsi        # 62ef <_IO_stdin_used+0x2ef>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2bdf:	49 89 c4             	mov    %rax,%r12
  thread_data[thread_count].task_count = total_barrier_count;
    2be2:	48 8b 05 17 3e 00 00 	mov    0x3e17(%rip),%rax        # 6a00 <_IO_stdin_used+0xa00>
    2be9:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].threads = thread_data;
    2bee:	4d 89 80 a0 03 00 00 	mov    %r8,0x3a0(%r8)
    2bf5:	4c 89 e5             	mov    %r12,%rbp
  thread_data[thread_count].task_count = total_barrier_count;
    2bf8:	49 89 80 b8 03 00 00 	mov    %rax,0x3b8(%r8)
    2bff:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2c01:	41 c7 80 a8 03 00 00 06 00 00 00 	movl   $0x6,0x3a8(%r8)
  thread_data[thread_count].thread_index = 0;
    2c0c:	49 c7 80 90 03 00 00 00 00 00 00 	movq   $0x0,0x390(%r8)
    2c17:	e8 14 f8 ff ff       	call   2430 <__printf_chk@plt>
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2c1c:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2c21:	49 8d 7c 24 30       	lea    0x30(%r12),%rdi
    2c26:	45 89 ec             	mov    %r13d,%r12d
    2c29:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
    2c30:	48 8d 15 59 0b 00 00 	lea    0xb59(%rip),%rdx        # 3790 <timer_thread>
    2c37:	49 89 ed             	mov    %rbp,%r13
    2c3a:	49 8d 88 90 03 00 00 	lea    0x390(%r8),%rcx
    2c41:	e8 0a f8 ff ff       	call   2450 <pthread_create@plt>
    2c46:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    2c4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    thread_data[x].type = WORKER;
    2c50:	41 c7 46 04 01 00 00 00 	movl   $0x1,0x4(%r14)
    2c58:	44 89 e2             	mov    %r12d,%edx
    2c5b:	bf 01 00 00 00       	mov    $0x1,%edi
    2c60:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2c62:	41 c7 46 2c 01 00 00 00 	movl   $0x1,0x2c(%r14)
    2c6a:	48 8d 35 57 39 00 00 	lea    0x3957(%rip),%rsi        # 65c8 <_IO_stdin_used+0x5c8>
  for (int x = 0 ; x < thread_count ; x++) {
    2c71:	41 83 c4 01          	add    $0x1,%r12d
    2c75:	e8 b6 f7 ff ff       	call   2430 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &timer_attr[x], &barriered_thread, &thread_data[x]);
    2c7a:	4c 89 f1             	mov    %r14,%rcx
    2c7d:	48 89 de             	mov    %rbx,%rsi
    2c80:	48 89 ef             	mov    %rbp,%rdi
    2c83:	4c 89 fa             	mov    %r15,%rdx
  for (int x = 0 ; x < thread_count ; x++) {
    2c86:	49 81 c6 98 00 00 00 	add    $0x98,%r14
    2c8d:	48 83 c5 08          	add    $0x8,%rbp
    2c91:	48 83 c3 38          	add    $0x38,%rbx
    pthread_create(&thread[x], &timer_attr[x], &barriered_thread, &thread_data[x]);
    2c95:	e8 b6 f7 ff ff       	call   2450 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2c9a:	41 83 fc 06          	cmp    $0x6,%r12d
    2c9e:	75 b0                	jne    2c50 <main+0x680>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    2ca0:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    2ca5:	48 8b 1d 5c 3d 00 00 	mov    0x3d5c(%rip),%rbx        # 6a08 <_IO_stdin_used+0xa08>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2cac:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    2cb1:	4d 89 ec             	mov    %r13,%r12
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2cb4:	bf 01 00 00 00       	mov    $0x1,%edi
    2cb9:	48 8d 2d 9f 36 00 00 	lea    0x369f(%rip),%rbp        # 635f <_IO_stdin_used+0x35f>
    thread_data[x].task_count = 0;
    2cc0:	49 89 98 50 04 00 00 	mov    %rbx,0x450(%r8)
    thread_data[x].type = IO;
    2cc7:	41 c7 80 2c 04 00 00 02 00 00 00 	movl   $0x2,0x42c(%r8)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2cd2:	e8 a9 f6 ff ff       	call   2380 <calloc@plt>
    2cd7:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2cdc:	be 00 08 00 00       	mov    $0x800,%esi
    2ce1:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2ce3:	49 89 80 68 04 00 00 	mov    %rax,0x468(%r8)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2cea:	e8 a1 f7 ff ff       	call   2490 <eventfd@plt>
    2cef:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2cf4:	ba 07 00 00 00       	mov    $0x7,%edx
    2cf9:	48 8d 35 0d 36 00 00 	lea    0x360d(%rip),%rsi        # 630d <_IO_stdin_used+0x30d>
    2d00:	bf 01 00 00 00       	mov    $0x1,%edi
    2d05:	41 89 80 70 04 00 00 	mov    %eax,0x470(%r8)
    2d0c:	31 c0                	xor    %eax,%eax
    thread_data[x].threads = thread_data;
    2d0e:	4d 89 80 38 04 00 00 	mov    %r8,0x438(%r8)
    thread_data[x].thread_count = thread_count;
    2d15:	41 c7 80 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r8)
    thread_data[x].thread_index = x;
    2d20:	41 c7 80 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r8)
    2d2b:	e8 00 f7 ff ff       	call   2430 <__printf_chk@plt>
    thread_data[x].type = IO;
    2d30:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2d35:	49 8d 7d 38          	lea    0x38(%r13),%rdi
    2d39:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    2d3e:	48 8d 15 1b 1d 00 00 	lea    0x1d1b(%rip),%rdx        # 4a60 <io_thread>
    thread_data[x].type = IO;
    2d45:	49 8d 88 28 04 00 00 	lea    0x428(%r8),%rcx
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2d4c:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    2d53:	e8 f8 f6 ff ff       	call   2450 <pthread_create@plt>
    2d58:	ba 08 00 00 00       	mov    $0x8,%edx
    2d5d:	48 8d 35 c0 35 00 00 	lea    0x35c0(%rip),%rsi        # 6324 <_IO_stdin_used+0x324>
    2d64:	31 c0                	xor    %eax,%eax
    2d66:	bf 01 00 00 00       	mov    $0x1,%edi
    2d6b:	e8 c0 f6 ff ff       	call   2430 <__printf_chk@plt>
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    2d70:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    thread_data[x].buffers = &buffers[buffer_index];
    2d75:	48 8b 44 24 38       	mov    0x38(%rsp),%rax

    thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2d7a:	49 8d 7d 40          	lea    0x40(%r13),%rdi
    2d7e:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    2d83:	48 8d 15 46 09 00 00 	lea    0x946(%rip),%rdx        # 36d0 <external_thread>
    2d8a:	4c 8d 6c 24 50       	lea    0x50(%rsp),%r13
    thread_data[x].buffers = &buffers[buffer_index];
    2d8f:	49 89 80 f8 04 00 00 	mov    %rax,0x4f8(%r8)
    thread_data[x].thread_count = thread_count;
    2d96:	48 8b 05 53 3c 00 00 	mov    0x3c53(%rip),%rax        # 69f0 <_IO_stdin_used+0x9f0>
    thread_data[x].type = EXTERNAL;
    2d9d:	49 8d 88 c0 04 00 00 	lea    0x4c0(%r8),%rcx
    thread_data[x].task_count = 0;
    2da4:	49 89 98 e8 04 00 00 	mov    %rbx,0x4e8(%r8)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2dab:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
    2db2:	31 db                	xor    %ebx,%ebx
    thread_data[x].thread_count = thread_count;
    2db4:	49 89 80 d8 04 00 00 	mov    %rax,0x4d8(%r8)
    thread_data[x].thread_index = x;
    2dbb:	48 8b 05 4e 3c 00 00 	mov    0x3c4e(%rip),%rax        # 6a10 <_IO_stdin_used+0xa10>
    thread_data[x].threads = thread_data;
    2dc2:	4d 89 80 d0 04 00 00 	mov    %r8,0x4d0(%r8)
    thread_data[x].thread_index = x;
    2dc9:	49 89 80 c0 04 00 00 	mov    %rax,0x4c0(%r8)
    thread_data[x].type = EXTERNAL;
    2dd0:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2dd5:	e8 76 f6 ff ff       	call   2450 <pthread_create@plt>
    2dda:	48 8d 3d 60 35 00 00 	lea    0x3560(%rip),%rdi        # 6341 <_IO_stdin_used+0x341>
    2de1:	e8 ea f4 ff ff       	call   22d0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    2de6:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    2deb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    void * result; 
    pthread_join(thread[x], &result);
    2df0:	49 8b 3c dc          	mov    (%r12,%rbx,8),%rdi
    2df4:	4c 89 ee             	mov    %r13,%rsi
    2df7:	e8 d4 f6 ff ff       	call   24d0 <pthread_join@plt>
    2dfc:	89 da                	mov    %ebx,%edx
    2dfe:	48 89 ee             	mov    %rbp,%rsi
    2e01:	bf 01 00 00 00       	mov    $0x1,%edi
    2e06:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    2e08:	48 83 c3 01          	add    $0x1,%rbx
    2e0c:	e8 1f f6 ff ff       	call   2430 <__printf_chk@plt>
    2e11:	48 83 fb 09          	cmp    $0x9,%rbx
    2e15:	75 d9                	jne    2df0 <main+0x820>
    2e17:	49 8d 86 b0 03 00 00 	lea    0x3b0(%r14),%rax
  }
  long total = 0;
  long v = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
    2e1e:	31 ed                	xor    %ebp,%ebp
  long sends = 0;
    2e20:	31 c9                	xor    %ecx,%ecx
  long v = 0;
    2e22:	45 31 c9             	xor    %r9d,%r9d
  long total = 0;
    2e25:	45 31 e4             	xor    %r12d,%r12d
    2e28:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  long ingests = 0;
    2e2d:	45 31 db             	xor    %r11d,%r11d
    2e30:	4d 8d 6e 20          	lea    0x20(%r14),%r13
    2e34:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
  long received = 0;
    2e39:	31 db                	xor    %ebx,%ebx
    2e3b:	4d 89 de             	mov    %r11,%r14
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
      struct timespec start = thread_data[x].start[n];
      struct timespec end = thread_data[x].end[n];
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    2e3e:	49 bf db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r15
    2e48:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2e4d:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    2e52:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    2e57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2e60:	49 63 45 08          	movslq 0x8(%r13),%rax
    2e64:	85 c0                	test   %eax,%eax
    2e66:	0f 8e af 00 00 00    	jle    2f1b <main+0x94b>
    2e6c:	49 8b 4d 00          	mov    0x0(%r13),%rcx
    2e70:	48 8d 34 80          	lea    (%rax,%rax,4),%rsi
    2e74:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    2e79:	48 c1 e6 07          	shl    $0x7,%rsi
    2e7d:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    2e82:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    2e87:	48 8d 91 08 01 00 00 	lea    0x108(%rcx),%rdx
    2e8e:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    2e93:	48 01 d6             	add    %rdx,%rsi
    2e96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      total += thread_data[x].tasks[n].n;
    2ea0:	48 03 0a             	add    (%rdx),%rcx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ea3:	48 8b 82 20 01 00 00 	mov    0x120(%rdx),%rax
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2eaa:	48 81 c2 80 02 00 00 	add    $0x280,%rdx
      v += thread_data[x].tasks[n].v;
    2eb1:	4c 03 9a 88 fd ff ff 	add    -0x278(%rdx),%r11
      ingests += thread_data[x].tasks[n].ingest_count;
    2eb8:	4c 03 b2 98 fe ff ff 	add    -0x168(%rdx),%r14
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ebf:	48 03 68 10          	add    0x10(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2ec3:	48 03 58 18          	add    0x18(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ec7:	48 03 68 30          	add    0x30(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2ecb:	48 03 58 38          	add    0x38(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ecf:	48 03 68 50          	add    0x50(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2ed3:	48 03 58 58          	add    0x58(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ed7:	48 03 68 70          	add    0x70(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2edb:	48 03 58 78          	add    0x78(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2edf:	48 03 a8 90 00 00 00 	add    0x90(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2ee6:	48 03 98 98 00 00 00 	add    0x98(%rax),%rbx
      sends += thread_data[x].tasks[n].sends;
    2eed:	4c 03 8a a8 fe ff ff 	add    -0x158(%rdx),%r9
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ef4:	48 03 a8 b0 00 00 00 	add    0xb0(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2efb:	48 03 98 b8 00 00 00 	add    0xb8(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2f02:	48 39 f2             	cmp    %rsi,%rdx
    2f05:	75 99                	jne    2ea0 <main+0x8d0>
    2f07:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    2f0c:	4c 89 5c 24 10       	mov    %r11,0x10(%rsp)
    2f11:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    2f16:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2f1b:	45 31 e4             	xor    %r12d,%r12d
    2f1e:	49 83 7d 50 00       	cmpq   $0x0,0x50(%r13)
    2f23:	7e 72                	jle    2f97 <main+0x9c7>
    2f25:	4c 89 ed             	mov    %r13,%rbp
    2f28:	49 89 dd             	mov    %rbx,%r13
    2f2b:	4c 89 e3             	mov    %r12,%rbx
    2f2e:	66 90                	xchg   %ax,%ax
      struct timespec start = thread_data[x].start[n];
    2f30:	48 8b 7d 30          	mov    0x30(%rbp),%rdi
    2f34:	48 89 de             	mov    %rbx,%rsi
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2f37:	48 83 c3 01          	add    $0x1,%rbx
    2f3b:	48 c1 e6 04          	shl    $0x4,%rsi
      struct timespec start = thread_data[x].start[n];
    2f3f:	48 01 f7             	add    %rsi,%rdi
      struct timespec end = thread_data[x].end[n];
    2f42:	48 03 75 38          	add    0x38(%rbp),%rsi
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    2f46:	48 8b 56 08          	mov    0x8(%rsi),%rdx
    2f4a:	48 2b 57 08          	sub    0x8(%rdi),%rdx
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    2f4e:	48 89 d0             	mov    %rdx,%rax
    2f51:	49 f7 e7             	mul    %r15
    2f54:	31 c0                	xor    %eax,%eax
    2f56:	48 89 d1             	mov    %rdx,%rcx
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    2f59:	48 8b 16             	mov    (%rsi),%rdx
    2f5c:	48 8d 35 10 34 00 00 	lea    0x3410(%rip),%rsi        # 6373 <_IO_stdin_used+0x373>
    2f63:	48 2b 17             	sub    (%rdi),%rdx
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    2f66:	48 c1 e9 12          	shr    $0x12,%rcx
    2f6a:	bf 01 00 00 00       	mov    $0x1,%edi
    2f6f:	e8 bc f4 ff ff       	call   2430 <__printf_chk@plt>
    2f74:	48 8b 55 40          	mov    0x40(%rbp),%rdx
    2f78:	bf 01 00 00 00       	mov    $0x1,%edi
    2f7d:	31 c0                	xor    %eax,%eax
    2f7f:	48 8d 35 0b 34 00 00 	lea    0x340b(%rip),%rsi        # 6391 <_IO_stdin_used+0x391>
    2f86:	e8 a5 f4 ff ff       	call   2430 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2f8b:	48 39 5d 50          	cmp    %rbx,0x50(%rbp)
    2f8f:	7f 9f                	jg     2f30 <main+0x960>
    2f91:	4c 89 eb             	mov    %r13,%rbx
    2f94:	49 89 ed             	mov    %rbp,%r13
      printf("%ld iterations\n", thread_data[x].iteration_count);
    }
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    2f97:	45 31 e4             	xor    %r12d,%r12d
    2f9a:	49 83 7d 68 00       	cmpq   $0x0,0x68(%r13)
    2f9f:	0f 8e 8a 00 00 00    	jle    302f <main+0xa5f>
    2fa5:	4c 89 ed             	mov    %r13,%rbp
    2fa8:	49 89 dd             	mov    %rbx,%r13
    2fab:	4c 89 e3             	mov    %r12,%rbx
    2fae:	66 90                	xchg   %ax,%ax
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    2fb0:	48 8b 45 58          	mov    0x58(%rbp),%rax
    2fb4:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    2fb8:	48 83 ec 08          	sub    $0x8,%rsp
    2fbc:	48 8d 35 2d 36 00 00 	lea    0x362d(%rip),%rsi        # 65f0 <_IO_stdin_used+0x5f0>
    2fc3:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    2fc8:	48 83 c3 01          	add    $0x1,%rbx
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    2fcc:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    2fd0:	4c 8b 61 18          	mov    0x18(%rcx),%r12
    2fd4:	4c 2b 61 08          	sub    0x8(%rcx),%r12
      printf("all %d task %d synchronized in %lds %ldms %ld ns \n", thread_count, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    2fd8:	4c 89 e0             	mov    %r12,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    2fdb:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    2fdf:	4c 2b 01             	sub    (%rcx),%r8
      printf("all %d task %d synchronized in %lds %ldms %ld ns \n", thread_count, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    2fe2:	49 f7 e7             	mul    %r15
    2fe5:	8b 49 20             	mov    0x20(%rcx),%ecx
    2fe8:	41 54                	push   %r12
    2fea:	31 c0                	xor    %eax,%eax
    2fec:	48 c1 ea 12          	shr    $0x12,%rdx
    2ff0:	49 89 d1             	mov    %rdx,%r9
    2ff3:	ba 06 00 00 00       	mov    $0x6,%edx
    2ff8:	e8 33 f4 ff ff       	call   2430 <__printf_chk@plt>
    2ffd:	48 8d 35 a9 33 00 00 	lea    0x33a9(%rip),%rsi        # 63ad <_IO_stdin_used+0x3ad>
    3004:	bf 01 00 00 00       	mov    $0x1,%edi
      printf("%ldns per thread\n", (seconds2 / thread_count));
    3009:	48 b8 ab aa aa aa aa aa aa aa 	movabs $0xaaaaaaaaaaaaaaab,%rax
    3013:	49 f7 e4             	mul    %r12
    3016:	31 c0                	xor    %eax,%eax
    3018:	48 c1 ea 02          	shr    $0x2,%rdx
    301c:	e8 0f f4 ff ff       	call   2430 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3021:	58                   	pop    %rax
    3022:	5a                   	pop    %rdx
    3023:	48 39 5d 68          	cmp    %rbx,0x68(%rbp)
    3027:	7f 87                	jg     2fb0 <main+0x9e0>
    3029:	4c 89 eb             	mov    %r13,%rbx
    302c:	49 89 ed             	mov    %rbp,%r13
    302f:	49 8b 55 70          	mov    0x70(%r13),%rdx
    3033:	48 8d 35 67 33 00 00 	lea    0x3367(%rip),%rsi        # 63a1 <_IO_stdin_used+0x3a1>
    303a:	bf 01 00 00 00       	mov    $0x1,%edi
    303f:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < thread_count ; x++) {
    3041:	49 81 c5 98 00 00 00 	add    $0x98,%r13
    3048:	e8 e3 f3 ff ff       	call   2430 <__printf_chk@plt>
    304d:	4c 39 6c 24 28       	cmp    %r13,0x28(%rsp)
    3052:	0f 85 08 fe ff ff    	jne    2e60 <main+0x890>
    3058:	4c 8b 64 24 08       	mov    0x8(%rsp),%r12
    305d:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    3062:	48 8d 35 56 33 00 00 	lea    0x3356(%rip),%rsi        # 63bf <_IO_stdin_used+0x3bf>
    3069:	31 c0                	xor    %eax,%eax
    306b:	bf 01 00 00 00       	mov    $0x1,%edi
    3070:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    3075:	4c 89 74 24 10       	mov    %r14,0x10(%rsp)
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total Protected %ld\n", protected_state->protected);
  printf("Total V %ld\n", v);
  printf("\n");
  printf("Total Protected per second %ld\n", protected_state->protected / DURATION);
    307a:	49 bd 89 88 88 88 88 88 88 88 	movabs $0x8888888888888889,%r13
    3084:	4c 89 e2             	mov    %r12,%rdx
    3087:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    308c:	e8 9f f3 ff ff       	call   2430 <__printf_chk@plt>
    3091:	bf 0a 00 00 00       	mov    $0xa,%edi
    3096:	e8 25 f2 ff ff       	call   22c0 <putchar@plt>
    309b:	4c 8b 74 24 40       	mov    0x40(%rsp),%r14
    30a0:	48 8d 35 2c 33 00 00 	lea    0x332c(%rip),%rsi        # 63d3 <_IO_stdin_used+0x3d3>
    30a7:	31 c0                	xor    %eax,%eax
    30a9:	bf 01 00 00 00       	mov    $0x1,%edi
    30ae:	49 8b 16             	mov    (%r14),%rdx
    30b1:	e8 7a f3 ff ff       	call   2430 <__printf_chk@plt>
    30b6:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    30bb:	48 8d 35 26 33 00 00 	lea    0x3326(%rip),%rsi        # 63e8 <_IO_stdin_used+0x3e8>
    30c2:	31 c0                	xor    %eax,%eax
    30c4:	bf 01 00 00 00       	mov    $0x1,%edi
    30c9:	e8 62 f3 ff ff       	call   2430 <__printf_chk@plt>
    30ce:	bf 0a 00 00 00       	mov    $0xa,%edi
    30d3:	e8 e8 f1 ff ff       	call   22c0 <putchar@plt>
    30d8:	49 8b 36             	mov    (%r14),%rsi
    30db:	bf 01 00 00 00       	mov    $0x1,%edi
    30e0:	48 89 f0             	mov    %rsi,%rax
    30e3:	49 f7 ed             	imul   %r13
    30e6:	31 c0                	xor    %eax,%eax
    30e8:	48 01 f2             	add    %rsi,%rdx
    30eb:	48 c1 fe 3f          	sar    $0x3f,%rsi
    30ef:	48 c1 fa 04          	sar    $0x4,%rdx
    30f3:	48 29 f2             	sub    %rsi,%rdx
    30f6:	48 8d 35 2b 35 00 00 	lea    0x352b(%rip),%rsi        # 6628 <_IO_stdin_used+0x628>
    30fd:	e8 2e f3 ff ff       	call   2430 <__printf_chk@plt>
    3102:	49 8b 56 08          	mov    0x8(%r14),%rdx
    3106:	bf 01 00 00 00       	mov    $0x1,%edi
    310b:	31 c0                	xor    %eax,%eax
    310d:	48 8d 35 34 35 00 00 	lea    0x3534(%rip),%rsi        # 6648 <_IO_stdin_used+0x648>
    3114:	e8 17 f3 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3119:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    311e:	bf 01 00 00 00       	mov    $0x1,%edi
    3123:	48 8d 35 46 35 00 00 	lea    0x3546(%rip),%rsi        # 6670 <_IO_stdin_used+0x670>
    312a:	4c 89 d8             	mov    %r11,%rax
    312d:	49 f7 ed             	imul   %r13
    3130:	31 c0                	xor    %eax,%eax
    3132:	4c 01 da             	add    %r11,%rdx
    3135:	49 c1 fb 3f          	sar    $0x3f,%r11
    3139:	48 c1 fa 04          	sar    $0x4,%rdx
    313d:	4c 29 da             	sub    %r11,%rdx
    3140:	e8 eb f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    3145:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    314a:	bf 01 00 00 00       	mov    $0x1,%edi
    314f:	48 8d 35 4a 35 00 00 	lea    0x354a(%rip),%rsi        # 66a0 <_IO_stdin_used+0x6a0>
    3156:	48 89 c8             	mov    %rcx,%rax
    3159:	49 f7 ed             	imul   %r13
    315c:	31 c0                	xor    %eax,%eax
    315e:	48 01 ca             	add    %rcx,%rdx
    3161:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3165:	48 c1 fa 04          	sar    $0x4,%rdx
    3169:	48 29 ca             	sub    %rcx,%rdx
    316c:	e8 bf f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    3171:	4c 89 e0             	mov    %r12,%rax
    3174:	bf 01 00 00 00       	mov    $0x1,%edi
    3179:	48 8d 35 50 35 00 00 	lea    0x3550(%rip),%rsi        # 66d0 <_IO_stdin_used+0x6d0>
    3180:	49 f7 ed             	imul   %r13
    3183:	4c 01 e2             	add    %r12,%rdx
    3186:	49 c1 fc 3f          	sar    $0x3f,%r12
    318a:	31 c0                	xor    %eax,%eax
    318c:	48 c1 fa 04          	sar    $0x4,%rdx
    3190:	4c 29 e2             	sub    %r12,%rdx
    3193:	e8 98 f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    3198:	48 89 e8             	mov    %rbp,%rax
    319b:	bf 01 00 00 00       	mov    $0x1,%edi
    31a0:	48 8d 35 4e 32 00 00 	lea    0x324e(%rip),%rsi        # 63f5 <_IO_stdin_used+0x3f5>
    31a7:	49 f7 ed             	imul   %r13
    31aa:	31 c0                	xor    %eax,%eax
    31ac:	48 01 ea             	add    %rbp,%rdx
    31af:	48 c1 fd 3f          	sar    $0x3f,%rbp
    31b3:	48 c1 fa 04          	sar    $0x4,%rdx
    31b7:	48 29 ea             	sub    %rbp,%rdx
    31ba:	e8 71 f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    31bf:	48 89 d8             	mov    %rbx,%rax
    31c2:	bf 01 00 00 00       	mov    $0x1,%edi
    31c7:	48 8d 35 38 32 00 00 	lea    0x3238(%rip),%rsi        # 6406 <_IO_stdin_used+0x406>
    31ce:	49 f7 ed             	imul   %r13
    31d1:	31 c0                	xor    %eax,%eax
    31d3:	48 01 da             	add    %rbx,%rdx
    31d6:	48 c1 fb 3f          	sar    $0x3f,%rbx
    31da:	48 c1 fa 04          	sar    $0x4,%rdx
    31de:	48 29 da             	sub    %rbx,%rdx
    31e1:	e8 4a f2 ff ff       	call   2430 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
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
          thread_data[x].tasks[y].run = barriered_work; 
    3210:	48 8d 05 39 20 00 00 	lea    0x2039(%rip),%rax        # 5250 <barriered_work>
    3217:	41 bd 06 00 00 00    	mov    $0x6,%r13d
    321d:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3224:	e9 20 f8 ff ff       	jmp    2a49 <main+0x479>
    3229:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            thread_data[x].tasks[y].protected = do_protected_write; 
    3230:	48 8d 05 09 01 00 00 	lea    0x109(%rip),%rax        # 3340 <do_protected_write>
    3237:	4b 89 84 27 20 01 00 00 	mov    %rax,0x120(%r15,%r12,1)
    323f:	e9 f6 f5 ff ff       	jmp    283a <main+0x26a>
}
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
int do_protected_write(struct BarrierTask *data) {
    3340:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    3344:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    334b:	48 8b 40 30          	mov    0x30(%rax),%rax
  data->v++; // thread local
    334f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    3357:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    335b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    335f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3366:	48 85 c9             	test   %rcx,%rcx
    3369:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3370:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3374:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    3378:	31 c0                	xor    %eax,%eax
    337a:	c3                   	ret
    337b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003380 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    3380:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    3384:	48 63 8f 84 01 00 00 	movslq 0x184(%rdi),%rcx
    338b:	85 c9                	test   %ecx,%ecx
    338d:	7e 6c                	jle    33fb <barriered_reset+0x7b>
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    338f:	48 63 87 30 01 00 00 	movslq 0x130(%rdi),%rax
    3396:	4c 8b 87 28 01 00 00 	mov    0x128(%rdi),%r8
    339d:	48 8d 0c 89          	lea    (%rcx,%rcx,4),%rcx
    33a1:	48 c1 e1 07          	shl    $0x7,%rcx
    33a5:	48 8d 3c c0          	lea    (%rax,%rax,8),%rdi
      data->thread->tasks[x].available = 1; 
    33a9:	49 8b 70 20          	mov    0x20(%r8),%rsi
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    33ad:	48 8d 04 78          	lea    (%rax,%rdi,2),%rax
    33b1:	49 8b 78 10          	mov    0x10(%r8),%rdi
    33b5:	48 8d 96 80 01 00 00 	lea    0x180(%rsi),%rdx
    33bc:	48 8d 8c 0e 80 01 00 00 	lea    0x180(%rsi,%rcx,1),%rcx
    33c4:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    33c8:	48 8b 40 20          	mov    0x20(%rax),%rax
    33cc:	48 05 00 01 00 00    	add    $0x100,%rax
    33d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    33d8:	83 40 80 01          	addl   $0x1,-0x80(%rax)
    for (int x = 0 ; x < data->task_count ; x++) {
    33dc:	48 81 c2 80 02 00 00 	add    $0x280,%rdx
      data->thread->threads[data->thread_index].tasks[x].prearrive++; 
    33e3:	83 00 01             	addl   $0x1,(%rax)
    for (int x = 0 ; x < data->task_count ; x++) {
    33e6:	48 05 80 02 00 00    	add    $0x280,%rax
      data->thread->tasks[x].available = 1; 
    33ec:	c7 82 80 fd ff ff 01 00 00 00 	movl   $0x1,-0x280(%rdx)
    for (int x = 0 ; x < data->task_count ; x++) {
    33f6:	48 39 ca             	cmp    %rcx,%rdx
    33f9:	75 dd                	jne    33d8 <barriered_reset+0x58>
  asm volatile ("mfence" ::: "memory");
    33fb:	0f ae f0             	mfence
}
    33fe:	31 c0                	xor    %eax,%eax
    3400:	c3                   	ret
    3401:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    340c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003410 <barriered_thread>:
void* barriered_thread(void *arg) {
    3410:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3414:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
    3418:	0f 85 aa 02 00 00    	jne    36c8 <barriered_thread+0x2b8>
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
    3446:	0f 8e 64 01 00 00    	jle    35b0 <barriered_thread+0x1a0>
    344c:	48 63 c3             	movslq %ebx,%rax
    344f:	48 8d 2c 80          	lea    (%rax,%rax,4),%rbp
    3453:	48 c1 e5 07          	shl    $0x7,%rbp
    3457:	eb 19                	jmp    3472 <barriered_thread+0x62>
    3459:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3460:	83 c3 01             	add    $0x1,%ebx
    3463:	48 81 c5 80 02 00 00 	add    $0x280,%rbp
    346a:	39 d3                	cmp    %edx,%ebx
    346c:	0f 8d 3e 01 00 00    	jge    35b0 <barriered_thread+0x1a0>
      if (data->tasks[t].available == 1) {
    3472:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    3477:	48 8d 0c 28          	lea    (%rax,%rbp,1),%rcx
    347b:	83 b9 80 01 00 00 01 	cmpl   $0x1,0x180(%rcx)
    3482:	75 dc                	jne    3460 <barriered_thread+0x50>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3484:	45 8b 44 24 18       	mov    0x18(%r12),%r8d
          previous = t - 1;
    3489:	83 ea 01             	sub    $0x1,%edx
    348c:	8d 73 ff             	lea    -0x1(%rbx),%esi
    348f:	85 db                	test   %ebx,%ebx
    3491:	0f 4f d6             	cmovg  %esi,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3494:	45 85 c0             	test   %r8d,%r8d
    3497:	0f 8e b3 01 00 00    	jle    3650 <barriered_thread+0x240>
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    349d:	48 63 d2             	movslq %edx,%rdx
    34a0:	44 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9d
        int prearrive = 0; 
    34a7:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    34aa:	45 31 f6             	xor    %r14d,%r14d
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    34ad:	48 8d 34 92          	lea    (%rdx,%rdx,4),%rsi
    34b1:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread].tasks[previous].prearrive == data->tasks[t].prearrive) {
    34b4:	8b b9 00 01 00 00    	mov    0x100(%rcx),%edi
    34ba:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    34bf:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    34c3:	48 c1 e6 07          	shl    $0x7,%rsi
    34c7:	48 8d 14 4a          	lea    (%rdx,%rcx,2),%rdx
    34cb:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    34cf:	90                   	nop
    34d0:	48 8b 50 20          	mov    0x20(%rax),%rdx
    34d4:	48 01 f2             	add    %rsi,%rdx
    34d7:	44 3b 8a 80 00 00 00 	cmp    0x80(%rdx),%r9d
    34de:	75 04                	jne    34e4 <barriered_thread+0xd4>
            arrived++;
    34e0:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread].tasks[previous].prearrive == data->tasks[t].prearrive) {
    34e4:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    34ea:	75 04                	jne    34f0 <barriered_thread+0xe0>
            prearrive++;
    34ec:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    34f0:	48 05 98 00 00 00    	add    $0x98,%rax
    34f6:	48 39 c8             	cmp    %rcx,%rax
    34f9:	75 d5                	jne    34d0 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    34fb:	45 39 d0             	cmp    %r10d,%r8d
    34fe:	0f 84 cc 00 00 00    	je     35d0 <barriered_thread+0x1c0>
    3504:	45 85 d2             	test   %r10d,%r10d
    3507:	0f 84 c3 00 00 00    	je     35d0 <barriered_thread+0x1c0>
        if (arrived == 0 || arrived == data->thread_count) {
    350d:	45 85 f6             	test   %r14d,%r14d
    3510:	74 0b                	je     351d <barriered_thread+0x10d>
    3512:	45 39 74 24 18       	cmp    %r14d,0x18(%r12)
    3517:	0f 85 93 00 00 00    	jne    35b0 <barriered_thread+0x1a0>
    351d:	49 8b 44 24 20       	mov    0x20(%r12),%rax
          data->tasks[t].prearrive++;
    3522:	48 01 e8             	add    %rbp,%rax
    3525:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    352c:	85 db                	test   %ebx,%ebx
    352e:	75 10                	jne    3540 <barriered_thread+0x130>
    3530:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
    3535:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
    353a:	0f 8c 68 01 00 00    	jl     36a8 <barriered_thread+0x298>
          data->tasks[t].available = 0;
    3540:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
          data->tasks[t].run(&data->threads[data->thread_index].tasks[t]);
    354a:	49 63 14 24          	movslq (%r12),%rdx
    354e:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    3552:	48 8d 14 4a          	lea    (%rdx,%rcx,2),%rdx
    3556:	49 8b 4c 24 10       	mov    0x10(%r12),%rcx
    355b:	48 8d 14 d1          	lea    (%rcx,%rdx,8),%rdx
    355f:	48 8b 7a 20          	mov    0x20(%rdx),%rdi
    3563:	48 01 ef             	add    %rbp,%rdi
    3566:	ff 90 18 01 00 00    	call   *0x118(%rax)
          data->tasks[t].arrived++;
    356c:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    3571:	48 01 e8             	add    %rbp,%rax
    3574:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    357b:	41 8b 44 24 28       	mov    0x28(%r12),%eax
          data->iteration_count++;
    3580:	49 83 44 24 60 01    	addq   $0x1,0x60(%r12)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3586:	83 e8 01             	sub    $0x1,%eax
    3589:	39 d8                	cmp    %ebx,%eax
    358b:	74 5b                	je     35e8 <barriered_thread+0x1d8>
          asm volatile ("mfence" ::: "memory");
    358d:	0f ae f0             	mfence
          if (waiting == 0) {
    3590:	45 85 ed             	test   %r13d,%r13d
    3593:	0f 84 7f 00 00 00    	je     3618 <barriered_thread+0x208>
    for (; t < data->task_count; t++) {
    3599:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    359e:	83 c3 01             	add    $0x1,%ebx
    35a1:	48 81 c5 80 02 00 00 	add    $0x280,%rbp
    35a8:	39 d3                	cmp    %edx,%ebx
    35aa:	0f 8c c2 fe ff ff    	jl     3472 <barriered_thread+0x62>
  while (data->running == 1) {
    35b0:	41 83 7c 24 2c 01    	cmpl   $0x1,0x2c(%r12)
    35b6:	0f 84 74 fe ff ff    	je     3430 <barriered_thread+0x20>
}
    35bc:	5b                   	pop    %rbx
    35bd:	31 c0                	xor    %eax,%eax
    35bf:	5d                   	pop    %rbp
    35c0:	41 5c                	pop    %r12
    35c2:	41 5d                	pop    %r13
    35c4:	41 5e                	pop    %r14
    35c6:	c3                   	ret
    35c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          if (waiting == 1) {
    35d0:	41 83 fd 01          	cmp    $0x1,%r13d
    35d4:	0f 84 86 00 00 00    	je     3660 <barriered_thread+0x250>
        int arrived = 0; 
    35da:	45 31 ed             	xor    %r13d,%r13d
    35dd:	e9 2b ff ff ff       	jmp    350d <barriered_thread+0xfd>
    35e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    35e8:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
    35ed:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
    35f2:	7d 99                	jge    358d <barriered_thread+0x17d>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    35f4:	48 c1 e6 04          	shl    $0x4,%rsi
    35f8:	bf 04 00 00 00       	mov    $0x4,%edi
    35fd:	49 03 74 24 58       	add    0x58(%r12),%rsi
    3602:	e8 e9 ec ff ff       	call   22f0 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    3607:	49 83 44 24 68 01    	addq   $0x1,0x68(%r12)
    360d:	e9 7b ff ff ff       	jmp    358d <barriered_thread+0x17d>
    3612:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    3618:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3620:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    3625:	41 bd 01 00 00 00    	mov    $0x1,%r13d
            data->task_snapshot[data->task_timestamp_count].task = t;
    362b:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    362f:	49 8b 44 24 78       	mov    0x78(%r12),%rax
    3634:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3638:	89 5e 20             	mov    %ebx,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    363b:	e8 b0 ec ff ff       	call   22f0 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    3640:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    3645:	e9 16 fe ff ff       	jmp    3460 <barriered_thread+0x50>
    364a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (waiting == 1) {
    3650:	41 83 fd 01          	cmp    $0x1,%r13d
    3654:	0f 85 c8 fe ff ff    	jne    3522 <barriered_thread+0x112>
        int arrived = 0; 
    365a:	45 31 f6             	xor    %r14d,%r14d
    365d:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    3660:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    3668:	bf 04 00 00 00       	mov    $0x4,%edi
    366d:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3671:	49 8b 44 24 78       	mov    0x78(%r12),%rax
    3676:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    367b:	e8 70 ec ff ff       	call   22f0 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    3680:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    3688:	48 83 c0 01          	add    $0x1,%rax
    368c:	48 99                	cqto
    368e:	49 f7 bc 24 88 00 00 00 	idivq  0x88(%r12)
    3696:	49 89 94 24 80 00 00 00 	mov    %rdx,0x80(%r12)
          if (waiting == 3) {
    369e:	e9 37 ff ff ff       	jmp    35da <barriered_thread+0x1ca>
    36a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    36a8:	48 c1 e6 04          	shl    $0x4,%rsi
    36ac:	bf 04 00 00 00       	mov    $0x4,%edi
    36b1:	49 03 74 24 50       	add    0x50(%r12),%rsi
    36b6:	e8 35 ec ff ff       	call   22f0 <clock_gettime@plt>
          data->tasks[t].available = 0;
    36bb:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    36c0:	48 01 e8             	add    %rbp,%rax
    36c3:	e9 78 fe ff ff       	jmp    3540 <barriered_thread+0x130>
}
    36c8:	31 c0                	xor    %eax,%eax
    36ca:	c3                   	ret
    36cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000036d0 <external_thread>:
void * external_thread(void *arg) {
    36d0:	f3 0f 1e fa          	endbr64
    36d4:	41 55                	push   %r13
    36d6:	41 54                	push   %r12
    36d8:	55                   	push   %rbp
    36d9:	53                   	push   %rbx
    36da:	48 83 ec 38          	sub    $0x38,%rsp
  struct timespec req = {
    36de:	66 0f 6f 05 0a 32 00 00 	movdqa 0x320a(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
void * external_thread(void *arg) {
    36e6:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    36ef:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    36f4:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
    36f6:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
  struct timespec req = {
    36fa:	0f 29 04 24          	movaps %xmm0,(%rsp)
  while (data->running == 1) {
    36fe:	75 64                	jne    3764 <external_thread+0x94>
    3700:	49 89 fd             	mov    %rdi,%r13
    3703:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3708:	48 89 e3             	mov    %rsp,%rbx
        data->buffers->buffer[x].data = "Hello world";
    370b:	4c 8d 25 f2 28 00 00 	lea    0x28f2(%rip),%r12        # 6004 <_IO_stdin_used+0x4>
    3712:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    nanosleep(&req , &rem);
    3718:	48 89 ee             	mov    %rbp,%rsi
    371b:	48 89 df             	mov    %rbx,%rdi
    371e:	e8 0d ec ff ff       	call   2330 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    3723:	49 8b 45 38          	mov    0x38(%r13),%rax
    3727:	48 63 10             	movslq (%rax),%rdx
    372a:	85 d2                	test   %edx,%edx
    372c:	7e 2c                	jle    375a <external_thread+0x8a>
    372e:	48 8b 40 08          	mov    0x8(%rax),%rax
    3732:	48 c1 e2 04          	shl    $0x4,%rdx
    3736:	48 01 c2             	add    %rax,%rdx
    3739:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    3740:	8b 48 08             	mov    0x8(%rax),%ecx
    3743:	85 c9                	test   %ecx,%ecx
    3745:	75 0a                	jne    3751 <external_thread+0x81>
        data->buffers->buffer[x].data = "Hello world";
    3747:	4c 89 20             	mov    %r12,(%rax)
        data->buffers->buffer[x].available = 1;
    374a:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    3751:	48 83 c0 10          	add    $0x10,%rax
    3755:	48 39 c2             	cmp    %rax,%rdx
    3758:	75 e6                	jne    3740 <external_thread+0x70>
    asm volatile ("mfence" ::: "memory");
    375a:	0f ae f0             	mfence
  while (data->running == 1) {
    375d:	41 83 7d 2c 01       	cmpl   $0x1,0x2c(%r13)
    3762:	74 b4                	je     3718 <external_thread+0x48>
}
    3764:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3769:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3772:	75 0d                	jne    3781 <external_thread+0xb1>
    3774:	48 83 c4 38          	add    $0x38,%rsp
    3778:	31 c0                	xor    %eax,%eax
    377a:	5b                   	pop    %rbx
    377b:	5d                   	pop    %rbp
    377c:	41 5c                	pop    %r12
    377e:	41 5d                	pop    %r13
    3780:	c3                   	ret
    3781:	e8 8a eb ff ff       	call   2310 <__stack_chk_fail@plt>
    3786:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003790 <timer_thread>:
void* timer_thread(void *arg) {
    3790:	f3 0f 1e fa          	endbr64
    3794:	41 57                	push   %r15
    3796:	48 8d 35 73 28 00 00 	lea    0x2873(%rip),%rsi        # 6010 <_IO_stdin_used+0x10>
    379d:	49 89 ff             	mov    %rdi,%r15
    37a0:	41 56                	push   %r14
    37a2:	41 55                	push   %r13
    37a4:	41 54                	push   %r12
    37a6:	55                   	push   %rbp
    37a7:	53                   	push   %rbx
    37a8:	48 83 ec 58          	sub    $0x58,%rsp
    37ac:	8b 17                	mov    (%rdi),%edx
    37ae:	bf 01 00 00 00       	mov    $0x1,%edi
    37b3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    37bc:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    37c1:	31 c0                	xor    %eax,%eax
    37c3:	e8 68 ec ff ff       	call   2430 <__printf_chk@plt>
  struct timespec preempt = {
    37c8:	66 0f 6f 05 20 31 00 00 	movdqa 0x3120(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
    37d0:	ba 30 75 00 00       	mov    $0x7530,%edx
    37d5:	31 c0                	xor    %eax,%eax
    37d7:	48 8d 35 44 28 00 00 	lea    0x2844(%rip),%rsi        # 6022 <_IO_stdin_used+0x22>
    37de:	bf 01 00 00 00       	mov    $0x1,%edi
    37e3:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    37e8:	e8 43 ec ff ff       	call   2430 <__printf_chk@plt>
  while (data->running && n < times) {
    37ed:	45 8b 6f 2c          	mov    0x2c(%r15),%r13d
    37f1:	45 85 ed             	test   %r13d,%r13d
    37f4:	0f 84 a3 00 00 00    	je     389d <timer_thread+0x10d>
  int n = 0;
    37fa:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    37fd:	45 31 ed             	xor    %r13d,%r13d
    3800:	49 89 e4             	mov    %rsp,%r12
    y++;
    3803:	31 db                	xor    %ebx,%ebx
    3805:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    380a:	48 89 ef             	mov    %rbp,%rdi
    380d:	4c 89 e6             	mov    %r12,%rsi
    n++;
    3810:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    3814:	e8 17 eb ff ff       	call   2330 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3819:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    381d:	41 8d 7d 01          	lea    0x1(%r13),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3821:	85 c0                	test   %eax,%eax
    3823:	7e 53                	jle    3878 <timer_thread+0xe8>
    3825:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    3829:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
        data->threads[x].tasks[y].scheduled = 0;
    382d:	4f 8d 44 ad 00       	lea    0x0(%r13,%r13,4),%r8
    3832:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    3836:	49 c1 e0 07          	shl    $0x7,%r8
    383a:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    383e:	66 90                	xchg   %ax,%ax
        int next = (y + 1) % data->threads[x].task_count;
    3840:	89 f8                	mov    %edi,%eax
        data->threads[x].tasks[next].scheduled = 1;
    3842:	48 8b 71 20          	mov    0x20(%rcx),%rsi
        int next = (y + 1) % data->threads[x].task_count;
    3846:	99                   	cltd
    3847:	f7 79 28             	idivl  0x28(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    384a:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
        data->threads[x].tasks[next].scheduled = 1;
    3851:	48 63 d2             	movslq %edx,%rdx
    3854:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
    3858:	48 c1 e0 07          	shl    $0x7,%rax
    385c:	c7 84 06 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rsi,%rax,1)
        data->threads[x].tasks[y].scheduled = 0;
    3867:	42 c7 84 06 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3873:	49 39 c9             	cmp    %rcx,%r9
    3876:	75 c8                	jne    3840 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
    3878:	0f ae f0             	mfence
    if (y >= data->threads[0].task_count) {
    387b:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
    387f:	41 8b 57 2c          	mov    0x2c(%r15),%edx
    y++;
    3883:	39 78 28             	cmp    %edi,0x28(%rax)
    3886:	0f 4e fb             	cmovle %ebx,%edi
    3889:	4c 63 ef             	movslq %edi,%r13
  while (data->running && n < times) {
    388c:	85 d2                	test   %edx,%edx
    388e:	74 0d                	je     389d <timer_thread+0x10d>
    3890:	41 81 fe 30 75 00 00 	cmp    $0x7530,%r14d
    3897:	0f 85 6d ff ff ff    	jne    380a <timer_thread+0x7a>
    389d:	48 8d 3d 94 27 00 00 	lea    0x2794(%rip),%rdi        # 6038 <_IO_stdin_used+0x38>
    38a4:	e8 27 ea ff ff       	call   22d0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    38a9:	49 63 47 1c          	movslq 0x1c(%r15),%rax
    38ad:	85 c0                	test   %eax,%eax
    38af:	0f 8e 8c 00 00 00    	jle    3941 <timer_thread+0x1b1>
    for (int y = 0 ; y < data->task_count ; y++) {
    38b5:	41 8b 57 28          	mov    0x28(%r15),%edx
    38b9:	85 d2                	test   %edx,%edx
    38bb:	0f 8e 80 00 00 00    	jle    3941 <timer_thread+0x1b1>
    38c1:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
      data->threads[x].tasks[y].sending = 0;
    38c5:	4d 8b 4f 10          	mov    0x10(%r15),%r9
    38c9:	48 8d 3c 48          	lea    (%rax,%rcx,2),%rdi
    38cd:	48 63 c2             	movslq %edx,%rax
    38d0:	31 c9                	xor    %ecx,%ecx
    38d2:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    38d6:	48 c1 e7 03          	shl    $0x3,%rdi
    38da:	48 c1 e0 07          	shl    $0x7,%rax
    38de:	4c 8d 80 38 02 00 00 	lea    0x238(%rax),%r8
    38e5:	49 8b 74 09 20       	mov    0x20(%r9,%rcx,1),%rsi
    38ea:	4a 8d 14 06          	lea    (%rsi,%r8,1),%rdx
    38ee:	48 8d 86 38 02 00 00 	lea    0x238(%rsi),%rax
    38f5:	49 89 d2             	mov    %rdx,%r10
    38f8:	49 29 c2             	sub    %rax,%r10
    38fb:	41 81 e2 80 00 00 00 	and    $0x80,%r10d
    3902:	74 16                	je     391a <timer_thread+0x18a>
    for (int y = 0 ; y < data->task_count ; y++) {
    3904:	48 8d 86 b8 04 00 00 	lea    0x4b8(%rsi),%rax
      data->threads[x].tasks[y].sending = 0;
    390b:	c7 86 38 02 00 00 00 00 00 00 	movl   $0x0,0x238(%rsi)
    for (int y = 0 ; y < data->task_count ; y++) {
    3915:	48 39 c2             	cmp    %rax,%rdx
    3918:	74 1b                	je     3935 <timer_thread+0x1a5>
      data->threads[x].tasks[y].sending = 0;
    391a:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3920:	48 05 00 05 00 00    	add    $0x500,%rax
      data->threads[x].tasks[y].sending = 0;
    3926:	c7 80 80 fd ff ff 00 00 00 00 	movl   $0x0,-0x280(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3930:	48 39 c2             	cmp    %rax,%rdx
    3933:	75 e5                	jne    391a <timer_thread+0x18a>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3935:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    393c:	48 39 cf             	cmp    %rcx,%rdi
    393f:	75 a4                	jne    38e5 <timer_thread+0x155>
  asm volatile ("mfence" ::: "memory");
    3941:	0f ae f0             	mfence
  struct timespec drain = {
    3944:	66 0f 6f 05 b4 2f 00 00 	movdqa 0x2fb4(%rip),%xmm0        # 6900 <_IO_stdin_used+0x900>
    394c:	48 8d 2d 0a 27 00 00 	lea    0x270a(%rip),%rbp        # 605d <_IO_stdin_used+0x5d>
    3953:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3958:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    395c:	41 8d 7d 01          	lea    0x1(%r13),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3960:	85 c0                	test   %eax,%eax
    3962:	7e 54                	jle    39b8 <timer_thread+0x228>
    3964:	49 8b 4f 10          	mov    0x10(%r15),%rcx
        data->threads[x].tasks[y].scheduled = 0;
    3968:	4d 63 ed             	movslq %r13d,%r13
    396b:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    396f:	4f 8d 44 ad 00       	lea    0x0(%r13,%r13,4),%r8
    3974:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    3978:	49 c1 e0 07          	shl    $0x7,%r8
    397c:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
        int next = (y + 1) % data->threads[x].task_count;
    3980:	89 f8                	mov    %edi,%eax
        data->threads[x].tasks[next].scheduled = 1;
    3982:	48 8b 71 20          	mov    0x20(%rcx),%rsi
        int next = (y + 1) % data->threads[x].task_count;
    3986:	99                   	cltd
    3987:	f7 79 28             	idivl  0x28(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    398a:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
        data->threads[x].tasks[next].scheduled = 1;
    3991:	48 63 c2             	movslq %edx,%rax
    3994:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3998:	48 c1 e0 07          	shl    $0x7,%rax
    399c:	c7 84 06 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rsi,%rax,1)
        data->threads[x].tasks[y].scheduled = 0;
    39a7:	42 c7 84 06 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    39b3:	4c 39 c9             	cmp    %r9,%rcx
    39b6:	75 c8                	jne    3980 <timer_thread+0x1f0>
    asm volatile ("mfence" ::: "memory");
    39b8:	0f ae f0             	mfence
    if (y >= data->threads[0].task_count) {
    39bb:	49 8b 57 10          	mov    0x10(%r15),%rdx
    y++;
    39bf:	45 31 ed             	xor    %r13d,%r13d
    39c2:	39 7a 28             	cmp    %edi,0x28(%rdx)
    39c5:	44 0f 4f ef          	cmovg  %edi,%r13d
    for (int x = 0 ; x < data->thread_count ; x++) {
    39c9:	41 8b 7f 18          	mov    0x18(%r15),%edi
    39cd:	85 ff                	test   %edi,%edi
    39cf:	0f 8e ae 00 00 00    	jle    3a83 <timer_thread+0x2f3>
    39d5:	31 db                	xor    %ebx,%ebx
    39d7:	45 31 e4             	xor    %r12d,%r12d
    39da:	41 b9 01 00 00 00    	mov    $0x1,%r9d
            all_empty = 0;
    39e0:	45 31 f6             	xor    %r14d,%r14d
    39e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    39e8:	4b 8d 04 b6          	lea    (%r14,%r14,4),%rax
    39ec:	48 c1 e0 07          	shl    $0x7,%rax
    39f0:	48 03 44 1a 20       	add    0x20(%rdx,%rbx,1),%rax
        for (int k = 0 ; k < data->thread_count; k++) {
    39f5:	31 d2                	xor    %edx,%edx
    39f7:	48 8b 80 28 02 00 00 	mov    0x228(%rax),%rax
    39fe:	eb 10                	jmp    3a10 <timer_thread+0x280>
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3a00:	4d 85 c0             	test   %r8,%r8
    3a03:	7f 25                	jg     3a2a <timer_thread+0x29a>
        for (int k = 0 ; k < data->thread_count; k++) {
    3a05:	83 c2 01             	add    $0x1,%edx
    3a08:	48 83 c0 20          	add    $0x20,%rax
    3a0c:	39 fa                	cmp    %edi,%edx
    3a0e:	74 30                	je     3a40 <timer_thread+0x2b0>
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3a10:	48 8b 08             	mov    (%rax),%rcx
    3a13:	48 8b 70 08          	mov    0x8(%rax),%rsi
    3a17:	48 8b 89 80 00 00 00 	mov    0x80(%rcx),%rcx
    3a1e:	4c 8b 86 80 00 00 00 	mov    0x80(%rsi),%r8
    3a25:	48 85 c9             	test   %rcx,%rcx
    3a28:	7e d6                	jle    3a00 <timer_thread+0x270>
    3a2a:	bf 01 00 00 00       	mov    $0x1,%edi
    3a2f:	48 89 ee             	mov    %rbp,%rsi
    3a32:	31 c0                	xor    %eax,%eax
    3a34:	e8 f7 e9 ff ff       	call   2430 <__printf_chk@plt>
            break;
    3a39:	41 8b 7f 18          	mov    0x18(%r15),%edi
            all_empty = 0;
    3a3d:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->thread_count ; y++) {
    3a40:	49 83 c6 01          	add    $0x1,%r14
    3a44:	44 39 f7             	cmp    %r14d,%edi
    3a47:	7e 07                	jle    3a50 <timer_thread+0x2c0>
    3a49:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3a4d:	eb 99                	jmp    39e8 <timer_thread+0x258>
    3a4f:	90                   	nop
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a50:	41 83 c4 01          	add    $0x1,%r12d
    3a54:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3a5b:	44 39 e7             	cmp    %r12d,%edi
    3a5e:	7e 09                	jle    3a69 <timer_thread+0x2d9>
    3a60:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3a64:	e9 77 ff ff ff       	jmp    39e0 <timer_thread+0x250>
    if (all_empty == 1) {
    3a69:	41 83 f9 01          	cmp    $0x1,%r9d
    3a6d:	74 14                	je     3a83 <timer_thread+0x2f3>
      nanosleep(&drain , &drainrem);
    3a6f:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3a74:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3a79:	e8 b2 e8 ff ff       	call   2330 <nanosleep@plt>
    3a7e:	e9 d5 fe ff ff       	jmp    3958 <timer_thread+0x1c8>
    3a83:	48 8d 3d ca 25 00 00 	lea    0x25ca(%rip),%rdi        # 6054 <_IO_stdin_used+0x54>
    3a8a:	e8 41 e8 ff ff       	call   22d0 <puts@plt>
  while (data->running) {
    3a8f:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    3a93:	85 c0                	test   %eax,%eax
    3a95:	0f 84 fb 00 00 00    	je     3b96 <timer_thread+0x406>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3a9b:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3a9f:	85 c9                	test   %ecx,%ecx
    3aa1:	7e 38                	jle    3adb <timer_thread+0x34b>
    3aa3:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3aa7:	31 db                	xor    %ebx,%ebx
    3aa9:	31 ed                	xor    %ebp,%ebp
    3aab:	4c 8d 25 bc 25 00 00 	lea    0x25bc(%rip),%r12        # 606e <_IO_stdin_used+0x6e>
    3ab2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->threads[x].running = 0;
    3ab8:	48 8d 04 1a          	lea    (%rdx,%rbx,1),%rax
      if (data->threads[x].type == IO) {
    3abc:	83 78 04 02          	cmpl   $0x2,0x4(%rax)
      data->threads[x].running = 0;
    3ac0:	c7 40 2c 00 00 00 00 	movl   $0x0,0x2c(%rax)
      if (data->threads[x].type == IO) {
    3ac7:	0f 84 f6 00 00 00    	je     3bc3 <timer_thread+0x433>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3acd:	83 c5 01             	add    $0x1,%ebp
    3ad0:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3ad7:	39 cd                	cmp    %ecx,%ebp
    3ad9:	7c dd                	jl     3ab8 <timer_thread+0x328>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3adb:	49 63 47 18          	movslq 0x18(%r15),%rax
    3adf:	85 c0                	test   %eax,%eax
    3ae1:	0f 8e 98 00 00 00    	jle    3b7f <timer_thread+0x3ef>
      for (int y = 0 ; y < data->task_count ; y++) {
    3ae7:	41 8b 57 28          	mov    0x28(%r15),%edx
    3aeb:	85 d2                	test   %edx,%edx
    3aed:	0f 8e 8c 00 00 00    	jle    3b7f <timer_thread+0x3ef>
    3af3:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
        data->threads[x].tasks[y].scheduled = 0;
    3af7:	4d 8b 57 10          	mov    0x10(%r15),%r10
    3afb:	4c 8d 04 48          	lea    (%rax,%rcx,2),%r8
    3aff:	48 63 c2             	movslq %edx,%rax
    3b02:	31 c9                	xor    %ecx,%ecx
    3b04:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3b08:	49 c1 e0 03          	shl    $0x3,%r8
    3b0c:	48 c1 e0 07          	shl    $0x7,%rax
    3b10:	4c 8d 88 00 02 00 00 	lea    0x200(%rax),%r9
    3b17:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3b20:	49 8b 74 0a 20       	mov    0x20(%r10,%rcx,1),%rsi
    3b25:	4a 8d 14 0e          	lea    (%rsi,%r9,1),%rdx
    3b29:	48 8d 86 00 02 00 00 	lea    0x200(%rsi),%rax
    3b30:	48 89 d7             	mov    %rdx,%rdi
    3b33:	48 29 c7             	sub    %rax,%rdi
    3b36:	81 e7 80 00 00 00    	and    $0x80,%edi
    3b3c:	74 1a                	je     3b58 <timer_thread+0x3c8>
      for (int y = 0 ; y < data->task_count ; y++) {
    3b3e:	48 8d 86 80 04 00 00 	lea    0x480(%rsi),%rax
        data->threads[x].tasks[y].scheduled = 0;
    3b45:	c7 86 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rsi)
      for (int y = 0 ; y < data->task_count ; y++) {
    3b4f:	48 39 d0             	cmp    %rdx,%rax
    3b52:	74 1f                	je     3b73 <timer_thread+0x3e3>
    3b54:	0f 1f 40 00          	nopl   0x0(%rax)
        data->threads[x].tasks[y].scheduled = 0;
    3b58:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3b5e:	48 05 00 05 00 00    	add    $0x500,%rax
        data->threads[x].tasks[y].scheduled = 0;
    3b64:	c7 80 80 fd ff ff 00 00 00 00 	movl   $0x0,-0x280(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3b6e:	48 39 d0             	cmp    %rdx,%rax
    3b71:	75 e5                	jne    3b58 <timer_thread+0x3c8>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b73:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3b7a:	4c 39 c1             	cmp    %r8,%rcx
    3b7d:	75 a1                	jne    3b20 <timer_thread+0x390>
    asm volatile ("mfence" ::: "memory");
    3b7f:	0f ae f0             	mfence
    3b82:	48 8d 3d f7 24 00 00 	lea    0x24f7(%rip),%rdi        # 6080 <_IO_stdin_used+0x80>
    3b89:	e8 42 e7 ff ff       	call   22d0 <puts@plt>
    data->running = 0;
    3b8e:	41 c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%r15)
    3b96:	48 8d 3d ea 24 00 00 	lea    0x24ea(%rip),%rdi        # 6087 <_IO_stdin_used+0x87>
    3b9d:	e8 2e e7 ff ff       	call   22d0 <puts@plt>
}
    3ba2:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3ba7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3bb0:	75 4a                	jne    3bfc <timer_thread+0x46c>
    3bb2:	48 83 c4 58          	add    $0x58,%rsp
    3bb6:	31 c0                	xor    %eax,%eax
    3bb8:	5b                   	pop    %rbx
    3bb9:	5d                   	pop    %rbp
    3bba:	41 5c                	pop    %r12
    3bbc:	41 5d                	pop    %r13
    3bbe:	41 5e                	pop    %r14
    3bc0:	41 5f                	pop    %r15
    3bc2:	c3                   	ret
    3bc3:	4c 89 e7             	mov    %r12,%rdi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3bc6:	83 c5 01             	add    $0x1,%ebp
    3bc9:	e8 02 e7 ff ff       	call   22d0 <puts@plt>
        eventfd_write(data->threads[x]._eventfd, 1);
    3bce:	49 8b 47 10          	mov    0x10(%r15),%rax
    3bd2:	be 01 00 00 00       	mov    $0x1,%esi
    3bd7:	8b 7c 18 48          	mov    0x48(%rax,%rbx,1),%edi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3bdb:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
        eventfd_write(data->threads[x]._eventfd, 1);
    3be2:	e8 f9 e7 ff ff       	call   23e0 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3be7:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3beb:	39 cd                	cmp    %ecx,%ebp
    3bed:	0f 8d e8 fe ff ff    	jge    3adb <timer_thread+0x34b>
    3bf3:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3bf7:	e9 bc fe ff ff       	jmp    3ab8 <timer_thread+0x328>
}
    3bfc:	e8 0f e7 ff ff       	call   2310 <__stack_chk_fail@plt>
    3c01:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3c0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003c10 <strtolower>:
void strtolower(char *str) {
    3c10:	f3 0f 1e fa          	endbr64
    3c14:	55                   	push   %rbp
    3c15:	53                   	push   %rbx
    3c16:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    3c1a:	48 0f be 1f          	movsbq (%rdi),%rbx
    3c1e:	84 db                	test   %bl,%bl
    3c20:	74 24                	je     3c46 <strtolower+0x36>
    3c22:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    3c25:	e8 c6 e8 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3c2a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3c30:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3c33:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    3c37:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3c3a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    3c3d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3c42:	84 db                	test   %bl,%bl
    3c44:	75 ea                	jne    3c30 <strtolower+0x20>
}
    3c46:	48 83 c4 08          	add    $0x8,%rsp
    3c4a:	5b                   	pop    %rbx
    3c4b:	5d                   	pop    %rbp
    3c4c:	c3                   	ret
    3c4d:	0f 1f 00             	nopl   (%rax)

0000000000003c50 <zh_malloc>:
void *zh_malloc(size_t size) {
    3c50:	f3 0f 1e fa          	endbr64
    3c54:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    3c58:	e8 93 e7 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3c5d:	48 85 c0             	test   %rax,%rax
    3c60:	74 05                	je     3c67 <zh_malloc+0x17>
}
    3c62:	48 83 c4 08          	add    $0x8,%rsp
    3c66:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3c67:	48 8b 0d b2 53 00 00 	mov    0x53b2(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    3c6e:	ba 28 00 00 00       	mov    $0x28,%edx
    3c73:	be 01 00 00 00       	mov    $0x1,%esi
    3c78:	48 8d 3d a1 27 00 00 	lea    0x27a1(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    3c7f:	e8 1c e8 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    3c84:	bf 01 00 00 00       	mov    $0x1,%edi
    3c89:	e8 f2 e7 ff ff       	call   2480 <exit@plt>
    3c8e:	66 90                	xchg   %ax,%ax

0000000000003c90 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3c90:	f3 0f 1e fa          	endbr64
    3c94:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    3c95:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3c9a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3c9d:	e8 9e e6 ff ff       	call   2340 <strrchr@plt>
    if (!dot || dot == filename)
    3ca2:	48 85 c0             	test   %rax,%rax
    3ca5:	74 11                	je     3cb8 <get_filename_ext+0x28>
    3ca7:	48 39 c3             	cmp    %rax,%rbx
    3caa:	74 0c                	je     3cb8 <get_filename_ext+0x28>
    return dot + 1;
    3cac:	48 83 c0 01          	add    $0x1,%rax
}
    3cb0:	5b                   	pop    %rbx
    3cb1:	c3                   	ret
    3cb2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    3cb8:	48 8d 05 10 24 00 00 	lea    0x2410(%rip),%rax        # 60cf <_IO_stdin_used+0xcf>
}
    3cbf:	5b                   	pop    %rbx
    3cc0:	c3                   	ret
    3cc1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3ccc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003cd0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    3cd0:	f3 0f 1e fa          	endbr64
    3cd4:	41 55                	push   %r13
    3cd6:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3cd9:	48 89 fe             	mov    %rdi,%rsi
    3cdc:	41 54                	push   %r12
    3cde:	55                   	push   %rbp
    3cdf:	48 89 d5             	mov    %rdx,%rbp
    3ce2:	ba 00 04 00 00       	mov    $0x400,%edx
    3ce7:	53                   	push   %rbx
    3ce8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    3cef:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3cf8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3d00:	31 c0                	xor    %eax,%eax
    3d02:	49 89 e4             	mov    %rsp,%r12
    3d05:	4c 89 e7             	mov    %r12,%rdi
    3d08:	e8 03 e7 ff ff       	call   2410 <__strcpy_chk@plt>
    for (; *str; ++str)
    3d0d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3d12:	84 db                	test   %bl,%bl
    3d14:	74 24                	je     3d3a <send_headers+0x6a>
        *str = (char)tolower(*str);
    3d16:	e8 d5 e7 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3d1b:	48 8b 08             	mov    (%rax),%rcx
    3d1e:	4c 89 e0             	mov    %r12,%rax
    3d21:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3d28:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    3d2b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    3d2f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    3d32:	48 0f be 18          	movsbq (%rax),%rbx
    3d36:	84 db                	test   %bl,%bl
    3d38:	75 ee                	jne    3d28 <send_headers+0x58>
    void *buf = malloc(size);
    3d3a:	bf 11 00 00 00       	mov    $0x11,%edi
    3d3f:	e8 ac e6 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3d44:	48 85 c0             	test   %rax,%rax
    3d47:	0f 84 7e 04 00 00    	je     41cb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3d4d:	66 0f 6f 05 bb 2b 00 00 	movdqa 0x2bbb(%rip),%xmm0        # 6910 <_IO_stdin_used+0x910>
    iov[0].iov_base = zh_malloc(slen);
    3d55:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    3d59:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    3d5e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3d66:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3d6a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    3d6d:	e8 7e e6 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3d72:	48 85 c0             	test   %rax,%rax
    3d75:	0f 84 50 04 00 00    	je     41cb <send_headers+0x4fb>
    3d7b:	66 0f 6f 05 9d 2b 00 00 	movdqa 0x2b9d(%rip),%xmm0        # 6920 <_IO_stdin_used+0x920>
    iov[1].iov_base = zh_malloc(slen);
    3d83:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    3d87:	4c 89 e7             	mov    %r12,%rdi
    3d8a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    3d94:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    3d9c:	0f 11 00             	movups %xmm0,(%rax)
    3d9f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    3da3:	be 2e 00 00 00       	mov    $0x2e,%esi
    3da8:	e8 93 e5 ff ff       	call   2340 <strrchr@plt>
    if (!dot || dot == filename)
    3dad:	48 85 c0             	test   %rax,%rax
    3db0:	0f 84 ea 02 00 00    	je     40a0 <send_headers+0x3d0>
    3db6:	4c 39 e0             	cmp    %r12,%rax
    3db9:	0f 84 e1 02 00 00    	je     40a0 <send_headers+0x3d0>
    return dot + 1;
    3dbf:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    3dc3:	48 8d 3d d3 22 00 00 	lea    0x22d3(%rip),%rdi        # 609d <_IO_stdin_used+0x9d>
    3dca:	48 89 de             	mov    %rbx,%rsi
    3dcd:	e8 be e5 ff ff       	call   2390 <strcmp@plt>
    3dd2:	85 c0                	test   %eax,%eax
    3dd4:	75 20                	jne    3df6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3dd6:	66 0f 6f 05 52 2b 00 00 	movdqa 0x2b52(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3dde:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3de6:	66 0f 6f 05 52 2b 00 00 	movdqa 0x2b52(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3dee:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    3df6:	48 89 de             	mov    %rbx,%rsi
    3df9:	48 8d 3d a1 22 00 00 	lea    0x22a1(%rip),%rdi        # 60a1 <_IO_stdin_used+0xa1>
    3e00:	e8 8b e5 ff ff       	call   2390 <strcmp@plt>
    3e05:	85 c0                	test   %eax,%eax
    3e07:	75 20                	jne    3e29 <send_headers+0x159>
    3e09:	66 0f 6f 05 1f 2b 00 00 	movdqa 0x2b1f(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3e11:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3e19:	66 0f 6f 05 1f 2b 00 00 	movdqa 0x2b1f(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3e21:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    3e29:	48 89 de             	mov    %rbx,%rsi
    3e2c:	48 8d 3d 73 22 00 00 	lea    0x2273(%rip),%rdi        # 60a6 <_IO_stdin_used+0xa6>
    3e33:	e8 58 e5 ff ff       	call   2390 <strcmp@plt>
    3e38:	85 c0                	test   %eax,%eax
    3e3a:	0f 84 10 02 00 00    	je     4050 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    3e40:	48 89 de             	mov    %rbx,%rsi
    3e43:	48 8d 3d 60 22 00 00 	lea    0x2260(%rip),%rdi        # 60aa <_IO_stdin_used+0xaa>
    3e4a:	e8 41 e5 ff ff       	call   2390 <strcmp@plt>
    3e4f:	85 c0                	test   %eax,%eax
    3e51:	0f 84 a9 02 00 00    	je     4100 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    3e57:	48 89 de             	mov    %rbx,%rsi
    3e5a:	48 8d 3d 4d 22 00 00 	lea    0x224d(%rip),%rdi        # 60ae <_IO_stdin_used+0xae>
    3e61:	e8 2a e5 ff ff       	call   2390 <strcmp@plt>
    3e66:	85 c0                	test   %eax,%eax
    3e68:	0f 84 6a 02 00 00    	je     40d8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    3e6e:	48 89 de             	mov    %rbx,%rsi
    3e71:	48 8d 3d 79 22 00 00 	lea    0x2279(%rip),%rdi        # 60f1 <_IO_stdin_used+0xf1>
    3e78:	e8 13 e5 ff ff       	call   2390 <strcmp@plt>
    3e7d:	85 c0                	test   %eax,%eax
    3e7f:	0f 84 2b 02 00 00    	je     40b0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    3e85:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3e88:	0f 84 52 01 00 00    	je     3fe0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    3e8e:	48 89 de             	mov    %rbx,%rsi
    3e91:	48 8d 3d 1a 22 00 00 	lea    0x221a(%rip),%rdi        # 60b2 <_IO_stdin_used+0xb2>
    3e98:	e8 f3 e4 ff ff       	call   2390 <strcmp@plt>
    3e9d:	85 c0                	test   %eax,%eax
    3e9f:	0f 84 ab 02 00 00    	je     4150 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    3ea5:	48 89 de             	mov    %rbx,%rsi
    3ea8:	48 8d 3d 07 22 00 00 	lea    0x2207(%rip),%rdi        # 60b6 <_IO_stdin_used+0xb6>
    3eaf:	e8 dc e4 ff ff       	call   2390 <strcmp@plt>
    3eb4:	85 c0                	test   %eax,%eax
    3eb6:	0f 84 6c 02 00 00    	je     4128 <send_headers+0x458>
    slen = strlen(send_buffer);
    3ebc:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    3ec4:	4c 89 e7             	mov    %r12,%rdi
    3ec7:	e8 34 e4 ff ff       	call   2300 <strlen@plt>
    void *buf = malloc(size);
    3ecc:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3ecf:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    3ed2:	e8 19 e5 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3ed7:	48 85 c0             	test   %rax,%rax
    3eda:	0f 84 eb 02 00 00    	je     41cb <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    3ee0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    3ee4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    3ee8:	83 fb 08             	cmp    $0x8,%ebx
    3eeb:	0f 83 3f 01 00 00    	jae    4030 <send_headers+0x360>
    3ef1:	f6 c3 04             	test   $0x4,%bl
    3ef4:	0f 85 7b 02 00 00    	jne    4175 <send_headers+0x4a5>
    3efa:	85 db                	test   %ebx,%ebx
    3efc:	74 13                	je     3f11 <send_headers+0x241>
    3efe:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3f06:	88 10                	mov    %dl,(%rax)
    3f08:	f6 c3 02             	test   $0x2,%bl
    3f0b:	0f 85 96 02 00 00    	jne    41a7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3f11:	4d 89 e8             	mov    %r13,%r8
    3f14:	48 8d 0d 9f 21 00 00 	lea    0x219f(%rip),%rcx        # 60ba <_IO_stdin_used+0xba>
    3f1b:	4c 89 e7             	mov    %r12,%rdi
    3f1e:	31 c0                	xor    %eax,%eax
    3f20:	ba 00 04 00 00       	mov    $0x400,%edx
    3f25:	be 01 00 00 00       	mov    $0x1,%esi
    3f2a:	e8 d1 e5 ff ff       	call   2500 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    3f2f:	4c 89 e7             	mov    %r12,%rdi
    3f32:	e8 c9 e3 ff ff       	call   2300 <strlen@plt>
    void *buf = malloc(size);
    3f37:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3f3a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    3f3d:	e8 ae e4 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3f42:	48 85 c0             	test   %rax,%rax
    3f45:	0f 84 80 02 00 00    	je     41cb <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    3f4b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    3f4f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    3f53:	83 fb 08             	cmp    $0x8,%ebx
    3f56:	0f 83 1c 01 00 00    	jae    4078 <send_headers+0x3a8>
    3f5c:	f6 c3 04             	test   $0x4,%bl
    3f5f:	0f 85 29 02 00 00    	jne    418e <send_headers+0x4be>
    3f65:	85 db                	test   %ebx,%ebx
    3f67:	74 13                	je     3f7c <send_headers+0x2ac>
    3f69:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3f71:	88 10                	mov    %dl,(%rax)
    3f73:	f6 c3 02             	test   $0x2,%bl
    3f76:	0f 85 3d 02 00 00    	jne    41b9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3f7c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    3f81:	bf 02 00 00 00       	mov    $0x2,%edi
    3f86:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    3f8e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    3f96:	e8 55 e4 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3f9b:	48 85 c0             	test   %rax,%rax
    3f9e:	0f 84 27 02 00 00    	je     41cb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3fa4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    3fac:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    3fb0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    3fb8:	66 89 10             	mov    %dx,(%rax)
}
    3fbb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    3fc3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3fcc:	0f 85 20 02 00 00    	jne    41f2 <send_headers+0x522>
    3fd2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    3fd9:	5b                   	pop    %rbx
    3fda:	5d                   	pop    %rbp
    3fdb:	41 5c                	pop    %r12
    3fdd:	41 5d                	pop    %r13
    3fdf:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    3fe0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    3fe4:	0f 85 a4 fe ff ff    	jne    3e8e <send_headers+0x1be>
    3fea:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    3fee:	0f 85 9a fe ff ff    	jne    3e8e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3ff4:	66 0f 6f 05 94 29 00 00 	movdqa 0x2994(%rip),%xmm0        # 6990 <_IO_stdin_used+0x990>
    3ffc:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4006:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    400e:	66 0f 6f 05 8a 29 00 00 	movdqa 0x298a(%rip),%xmm0        # 69a0 <_IO_stdin_used+0x9a0>
    4016:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    401e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4026:	e9 63 fe ff ff       	jmp    3e8e <send_headers+0x1be>
    402b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4030:	89 da                	mov    %ebx,%edx
    4032:	48 89 c7             	mov    %rax,%rdi
    4035:	4c 89 e6             	mov    %r12,%rsi
    4038:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    403d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4042:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4045:	c1 e9 03             	shr    $0x3,%ecx
    4048:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    404b:	e9 c1 fe ff ff       	jmp    3f11 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4050:	66 0f 6f 05 d8 28 00 00 	movdqa 0x28d8(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    4058:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4060:	66 0f 6f 05 e8 28 00 00 	movdqa 0x28e8(%rip),%xmm0        # 6950 <_IO_stdin_used+0x950>
    4068:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4070:	e9 cb fd ff ff       	jmp    3e40 <send_headers+0x170>
    4075:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4078:	89 da                	mov    %ebx,%edx
    407a:	48 89 c7             	mov    %rax,%rdi
    407d:	4c 89 e6             	mov    %r12,%rsi
    4080:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4085:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    408a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    408d:	c1 e9 03             	shr    $0x3,%ecx
    4090:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4093:	e9 e4 fe ff ff       	jmp    3f7c <send_headers+0x2ac>
    4098:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    40a0:	48 8d 1d 28 20 00 00 	lea    0x2028(%rip),%rbx        # 60cf <_IO_stdin_used+0xcf>
    40a7:	e9 94 fd ff ff       	jmp    3e40 <send_headers+0x170>
    40ac:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    40b0:	66 0f 6f 05 b8 28 00 00 	movdqa 0x28b8(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    40b8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40c0:	66 0f 6f 05 b8 28 00 00 	movdqa 0x28b8(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    40c8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    40d0:	e9 b0 fd ff ff       	jmp    3e85 <send_headers+0x1b5>
    40d5:	0f 1f 00             	nopl   (%rax)
    40d8:	66 0f 6f 05 90 28 00 00 	movdqa 0x2890(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    40e0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40e8:	66 0f 6f 05 90 28 00 00 	movdqa 0x2890(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    40f0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    40f8:	e9 71 fd ff ff       	jmp    3e6e <send_headers+0x19e>
    40fd:	0f 1f 00             	nopl   (%rax)
    4100:	66 0f 6f 05 28 28 00 00 	movdqa 0x2828(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    4108:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4110:	66 0f 6f 05 48 28 00 00 	movdqa 0x2848(%rip),%xmm0        # 6960 <_IO_stdin_used+0x960>
    4118:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4120:	e9 32 fd ff ff       	jmp    3e57 <send_headers+0x187>
    4125:	0f 1f 00             	nopl   (%rax)
    4128:	66 0f 6f 05 40 28 00 00 	movdqa 0x2840(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4130:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4138:	66 0f 6f 05 80 28 00 00 	movdqa 0x2880(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    4140:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4148:	e9 6f fd ff ff       	jmp    3ebc <send_headers+0x1ec>
    414d:	0f 1f 00             	nopl   (%rax)
    4150:	66 0f 6f 05 18 28 00 00 	movdqa 0x2818(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4158:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4160:	66 0f 6f 05 48 28 00 00 	movdqa 0x2848(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    4168:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4170:	e9 30 fd ff ff       	jmp    3ea5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4175:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    417c:	89 db                	mov    %ebx,%ebx
    417e:	89 10                	mov    %edx,(%rax)
    4180:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4185:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4189:	e9 83 fd ff ff       	jmp    3f11 <send_headers+0x241>
    418e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4195:	89 db                	mov    %ebx,%ebx
    4197:	89 10                	mov    %edx,(%rax)
    4199:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    419e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    41a2:	e9 d5 fd ff ff       	jmp    3f7c <send_headers+0x2ac>
    41a7:	89 db                	mov    %ebx,%ebx
    41a9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    41af:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    41b4:	e9 58 fd ff ff       	jmp    3f11 <send_headers+0x241>
    41b9:	89 db                	mov    %ebx,%ebx
    41bb:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    41c1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    41c6:	e9 b1 fd ff ff       	jmp    3f7c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    41cb:	48 8b 0d 4e 4e 00 00 	mov    0x4e4e(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    41d2:	ba 28 00 00 00       	mov    $0x28,%edx
    41d7:	be 01 00 00 00       	mov    $0x1,%esi
    41dc:	48 8d 3d 3d 22 00 00 	lea    0x223d(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    41e3:	e8 b8 e2 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    41e8:	bf 01 00 00 00       	mov    $0x1,%edi
    41ed:	e8 8e e2 ff ff       	call   2480 <exit@plt>
}
    41f2:	e8 19 e1 ff ff       	call   2310 <__stack_chk_fail@plt>
    41f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004200 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4200:	f3 0f 1e fa          	endbr64
    4204:	41 55                	push   %r13
    4206:	49 89 d5             	mov    %rdx,%r13
    4209:	41 54                	push   %r12
    420b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    420e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4211:	55                   	push   %rbp
    4212:	53                   	push   %rbx
    4213:	48 89 f3             	mov    %rsi,%rbx
    4216:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    421a:	e8 d1 e1 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    421f:	48 85 c0             	test   %rax,%rax
    4222:	74 6b                	je     428f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4224:	4c 89 e7             	mov    %r12,%rdi
    4227:	48 89 c5             	mov    %rax,%rbp
    422a:	31 f6                	xor    %esi,%esi
    422c:	31 c0                	xor    %eax,%eax
    422e:	e8 2d e2 ff ff       	call   2460 <open@plt>
    4233:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4236:	85 c0                	test   %eax,%eax
    4238:	0f 88 f8 e2 ff ff    	js     2536 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    423e:	48 89 da             	mov    %rbx,%rdx
    4241:	48 89 ee             	mov    %rbp,%rsi
    4244:	89 c7                	mov    %eax,%edi
    4246:	e8 25 e1 ff ff       	call   2370 <read@plt>
    if (ret < file_size) {
    424b:	48 98                	cltq
    424d:	48 39 d8             	cmp    %rbx,%rax
    4250:	7c 1e                	jl     4270 <copy_file_contents+0x70>
    close(fd);
    4252:	44 89 e7             	mov    %r12d,%edi
    4255:	e8 f6 e0 ff ff       	call   2350 <close@plt>
    iov->iov_base = buf;
    425a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    425e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4262:	48 83 c4 08          	add    $0x8,%rsp
    4266:	5b                   	pop    %rbx
    4267:	5d                   	pop    %rbp
    4268:	41 5c                	pop    %r12
    426a:	41 5d                	pop    %r13
    426c:	c3                   	ret
    426d:	0f 1f 00             	nopl   (%rax)
    4270:	48 8b 0d a9 4d 00 00 	mov    0x4da9(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4277:	ba 1a 00 00 00       	mov    $0x1a,%edx
    427c:	be 01 00 00 00       	mov    $0x1,%esi
    4281:	48 8d 3d 48 1e 00 00 	lea    0x1e48(%rip),%rdi        # 60d0 <_IO_stdin_used+0xd0>
    4288:	e8 13 e2 ff ff       	call   24a0 <fwrite@plt>
    428d:	eb c3                	jmp    4252 <copy_file_contents+0x52>
    428f:	48 8b 0d 8a 4d 00 00 	mov    0x4d8a(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4296:	ba 28 00 00 00       	mov    $0x28,%edx
    429b:	be 01 00 00 00       	mov    $0x1,%esi
    42a0:	48 8d 3d 79 21 00 00 	lea    0x2179(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    42a7:	e8 f4 e1 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    42ac:	bf 01 00 00 00       	mov    $0x1,%edi
    42b1:	e8 ca e1 ff ff       	call   2480 <exit@plt>
    42b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000042c0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    42c0:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    42c4:	8b 46 44             	mov    0x44(%rsi),%eax
    42c7:	48 89 fa             	mov    %rdi,%rdx
    42ca:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    42cd:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    42d3:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    42d6:	48 8b 07             	mov    (%rdi),%rax
    42d9:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    42dc:	f6 c1 02             	test   $0x2,%cl
    42df:	74 00                	je     42e1 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    42e1:	89 f0                	mov    %esi,%eax
    42e3:	44 29 c0             	sub    %r8d,%eax
    42e6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    42e9:	0f 82 53 e2 ff ff    	jb     2542 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    42ef:	c1 e9 0a             	shr    $0xa,%ecx
    42f2:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    42f6:	8b 47 44             	mov    0x44(%rdi),%eax
    42f9:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    42fc:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    42ff:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4302:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4305:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4309:	d3 e0                	shl    %cl,%eax
    430b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    430e:	48 c1 e0 06          	shl    $0x6,%rax
    4312:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4316:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    431c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    431f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4323:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4329:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4331:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4335:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4338:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    433f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4347:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    434b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    434f:	e8 cc df ff ff       	call   2320 <io_uring_submit@plt>
}
    4354:	31 c0                	xor    %eax,%eax
    4356:	48 83 c4 08          	add    $0x8,%rsp
    435a:	c3                   	ret
    435b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004360 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    4360:	f3 0f 1e fa          	endbr64
    4364:	41 55                	push   %r13
    4366:	41 89 fd             	mov    %edi,%r13d
    4369:	41 54                	push   %r12
    436b:	55                   	push   %rbp
    436c:	53                   	push   %rbx
    436d:	48 89 f3             	mov    %rsi,%rbx
    4370:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4374:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4377:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    437d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    4380:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4383:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4385:	f6 c1 02             	test   $0x2,%cl
    4388:	74 00                	je     438a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    438a:	89 c2                	mov    %eax,%edx
    438c:	29 f2                	sub    %esi,%edx
    438e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4391:	0f 82 bb e1 ff ff    	jb     2552 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4397:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    439a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    439d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    43a0:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    43a5:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    43a8:	23 6b 58             	and    0x58(%rbx),%ebp
    43ab:	d3 e5                	shl    %cl,%ebp
    43ad:	48 c1 e5 06          	shl    $0x6,%rbp
    43b1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    43b5:	e8 36 e0 ff ff       	call   23f0 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    43ba:	be 01 00 00 00       	mov    $0x1,%esi
    43bf:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    43c4:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    43c7:	e8 b4 df ff ff       	call   2380 <calloc@plt>
    req->client_socket = client_socket;
    43cc:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    43d1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    43d5:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    43d8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    43dd:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    43e2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    43eb:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    43f3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    43f7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    43fb:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4402:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    440a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    440e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4416:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    441e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4422:	e8 f9 de ff ff       	call   2320 <io_uring_submit@plt>
}
    4427:	48 83 c4 08          	add    $0x8,%rsp
    442b:	31 c0                	xor    %eax,%eax
    442d:	5b                   	pop    %rbx
    442e:	5d                   	pop    %rbp
    442f:	41 5c                	pop    %r12
    4431:	41 5d                	pop    %r13
    4433:	c3                   	ret
    4434:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    443f:	90                   	nop

0000000000004440 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4440:	f3 0f 1e fa          	endbr64
    4444:	41 56                	push   %r14
    4446:	41 89 f6             	mov    %esi,%r14d
    4449:	41 55                	push   %r13
    444b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    444e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4453:	41 54                	push   %r12
    4455:	55                   	push   %rbp
    4456:	48 89 d5             	mov    %rdx,%rbp
    4459:	53                   	push   %rbx
    void *buf = malloc(size);
    445a:	e8 91 df ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    445f:	48 85 c0             	test   %rax,%rax
    4462:	0f 84 dd 00 00 00    	je     4545 <_send_static_string_content+0x105>
    4468:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    446b:	4c 89 ef             	mov    %r13,%rdi
    446e:	e8 8d de ff ff       	call   2300 <strlen@plt>
    req->iovec_count = 1;
    4473:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    447a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    447e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    4481:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    4484:	e8 67 df ff ff       	call   23f0 <malloc@plt>
    4489:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    448c:	48 85 c0             	test   %rax,%rax
    448f:	0f 84 b0 00 00 00    	je     4545 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    4495:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4499:	4c 89 e2             	mov    %r12,%rdx
    449c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    449f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    44a3:	e8 18 df ff ff       	call   23c0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    44a8:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    44ab:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    44b1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    44b4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    44b8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    44ba:	f6 c1 02             	test   $0x2,%cl
    44bd:	0f 85 7d 00 00 00    	jne    4540 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    44c3:	89 d0                	mov    %edx,%eax
    44c5:	29 f0                	sub    %esi,%eax
    44c7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    44ca:	0f 82 8c e0 ff ff    	jb     255c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    44d0:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    44d3:	8b 45 44             	mov    0x44(%rbp),%eax
    44d6:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    44d9:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    44dc:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    44df:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    44e2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    44e8:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    44ec:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    44ee:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    44f1:	48 89 ef             	mov    %rbp,%rdi
    44f4:	48 c1 e0 06          	shl    $0x6,%rax
    44f8:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    44fc:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    44ff:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4503:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4509:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4511:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4515:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4518:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    451f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4527:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    452b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    452f:	5b                   	pop    %rbx
    4530:	5d                   	pop    %rbp
    4531:	41 5c                	pop    %r12
    4533:	41 5d                	pop    %r13
    4535:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4537:	e9 e4 dd ff ff       	jmp    2320 <io_uring_submit@plt>
    453c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4540:	e9 7e ff ff ff       	jmp    44c3 <_send_static_string_content+0x83>
    4545:	48 8b 0d d4 4a 00 00 	mov    0x4ad4(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    454c:	ba 28 00 00 00       	mov    $0x28,%edx
    4551:	be 01 00 00 00       	mov    $0x1,%esi
    4556:	48 8d 3d c3 1e 00 00 	lea    0x1ec3(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    455d:	e8 3e df ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    4562:	bf 01 00 00 00       	mov    $0x1,%edi
    4567:	e8 14 df ff ff       	call   2480 <exit@plt>
    456c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004570 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    4570:	f3 0f 1e fa          	endbr64
    4574:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4577:	89 fe                	mov    %edi,%esi
    4579:	48 8b 3d 98 4a 00 00 	mov    0x4a98(%rip),%rdi        # 9018 <unimplemented_content>
    4580:	e9 bb fe ff ff       	jmp    4440 <_send_static_string_content>
    4585:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004590 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    4590:	f3 0f 1e fa          	endbr64
    4594:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    4597:	89 fe                	mov    %edi,%esi
    4599:	48 8b 3d 70 4a 00 00 	mov    0x4a70(%rip),%rdi        # 9010 <http_404_content>
    45a0:	e9 9b fe ff ff       	jmp    4440 <_send_static_string_content>
    45a5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000045b0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    45b0:	f3 0f 1e fa          	endbr64
    45b4:	41 56                	push   %r14
    45b6:	41 55                	push   %r13
    45b8:	49 89 d5             	mov    %rdx,%r13
    45bb:	41 54                	push   %r12
    45bd:	41 89 f4             	mov    %esi,%r12d
    45c0:	55                   	push   %rbp
    45c1:	48 89 fd             	mov    %rdi,%rbp
    45c4:	53                   	push   %rbx
    45c5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    45cc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    45d5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    45dd:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    45df:	e8 1c dd ff ff       	call   2300 <strlen@plt>
    45e4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    45e9:	48 89 c3             	mov    %rax,%rbx
    45ec:	0f 84 b6 00 00 00    	je     46a8 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    45f2:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    45f7:	48 89 ee             	mov    %rbp,%rsi
    45fa:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    45fe:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4603:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    460b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4613:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    461e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4626:	e8 75 dd ff ff       	call   23a0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    462b:	48 89 e6             	mov    %rsp,%rsi
    462e:	4c 89 f7             	mov    %r14,%rdi
    4631:	e8 7a dd ff ff       	call   23b0 <stat@plt>
    4636:	83 f8 ff             	cmp    $0xffffffff,%eax
    4639:	0f 84 d3 00 00 00    	je     4712 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    463f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4643:	25 00 f0 00 00       	and    $0xf000,%eax
    4648:	3d 00 80 00 00       	cmp    $0x8000,%eax
    464d:	0f 84 f5 00 00 00    	je     4748 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    4653:	48 8b 3d b6 49 00 00 	mov    0x49b6(%rip),%rdi        # 9010 <http_404_content>
    465a:	4c 89 ea             	mov    %r13,%rdx
    465d:	44 89 e6             	mov    %r12d,%esi
    4660:	e8 db fd ff ff       	call   4440 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4665:	4c 89 f2             	mov    %r14,%rdx
    4668:	bf 01 00 00 00       	mov    $0x1,%edi
    466d:	31 c0                	xor    %eax,%eax
    466f:	48 8d 35 aa 1a 00 00 	lea    0x1aaa(%rip),%rsi        # 6120 <_IO_stdin_used+0x120>
    4676:	e8 b5 dd ff ff       	call   2430 <__printf_chk@plt>
}
    467b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4683:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    468c:	0f 85 20 01 00 00    	jne    47b2 <handle_get_method+0x202>
    4692:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    4699:	5b                   	pop    %rbx
    469a:	5d                   	pop    %rbp
    469b:	41 5c                	pop    %r12
    469d:	41 5d                	pop    %r13
    469f:	41 5e                	pop    %r14
    46a1:	c3                   	ret
    46a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    46a8:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    46ad:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    46b5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    46ba:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    46bd:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    46c5:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    46c8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    46d0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    46db:	e8 c0 dc ff ff       	call   23a0 <__memcpy_chk@plt>
    46e0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    46e5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    46ea:	48 8d 35 fa 19 00 00 	lea    0x19fa(%rip),%rsi        # 60eb <_IO_stdin_used+0xeb>
    46f1:	48 29 d9             	sub    %rbx,%rcx
    46f4:	ba 0b 00 00 00       	mov    $0xb,%edx
    46f9:	e8 a2 dc ff ff       	call   23a0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    46fe:	48 89 e6             	mov    %rsp,%rsi
    4701:	4c 89 f7             	mov    %r14,%rdi
    4704:	e8 a7 dc ff ff       	call   23b0 <stat@plt>
    4709:	83 f8 ff             	cmp    $0xffffffff,%eax
    470c:	0f 85 2d ff ff ff    	jne    463f <handle_get_method+0x8f>
    4712:	4c 89 f2             	mov    %r14,%rdx
    4715:	48 89 e9             	mov    %rbp,%rcx
    4718:	48 8d 35 d7 19 00 00 	lea    0x19d7(%rip),%rsi        # 60f6 <_IO_stdin_used+0xf6>
    471f:	31 c0                	xor    %eax,%eax
    4721:	bf 01 00 00 00       	mov    $0x1,%edi
    4726:	e8 05 dd ff ff       	call   2430 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    472b:	48 8b 3d de 48 00 00 	mov    0x48de(%rip),%rdi        # 9010 <http_404_content>
    4732:	4c 89 ea             	mov    %r13,%rdx
    4735:	44 89 e6             	mov    %r12d,%esi
    4738:	e8 03 fd ff ff       	call   4440 <_send_static_string_content>
}
    473d:	e9 39 ff ff ff       	jmp    467b <handle_get_method+0xcb>
    4742:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4748:	bf 70 00 00 00       	mov    $0x70,%edi
    474d:	e8 9e dc ff ff       	call   23f0 <malloc@plt>
    4752:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    4755:	48 85 c0             	test   %rax,%rax
    4758:	74 5d                	je     47b7 <handle_get_method+0x207>
            req->client_socket = client_socket;
    475a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    475e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4763:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4767:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    476a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    4771:	e8 5a f5 ff ff       	call   3cd0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    4776:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    477b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    477f:	4c 89 f7             	mov    %r14,%rdi
    4782:	e8 79 fa ff ff       	call   4200 <copy_file_contents>
    4787:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    478c:	4c 89 f2             	mov    %r14,%rdx
    478f:	31 c0                	xor    %eax,%eax
    4791:	48 8d 35 76 19 00 00 	lea    0x1976(%rip),%rsi        # 610e <_IO_stdin_used+0x10e>
    4798:	bf 01 00 00 00       	mov    $0x1,%edi
    479d:	e8 8e dc ff ff       	call   2430 <__printf_chk@plt>
            add_write_request(req, ring);
    47a2:	4c 89 ee             	mov    %r13,%rsi
    47a5:	48 89 df             	mov    %rbx,%rdi
    47a8:	e8 13 fb ff ff       	call   42c0 <add_write_request>
    47ad:	e9 c9 fe ff ff       	jmp    467b <handle_get_method+0xcb>
}
    47b2:	e8 59 db ff ff       	call   2310 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    47b7:	48 8b 0d 62 48 00 00 	mov    0x4862(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    47be:	ba 28 00 00 00       	mov    $0x28,%edx
    47c3:	be 01 00 00 00       	mov    $0x1,%esi
    47c8:	48 8d 3d 51 1c 00 00 	lea    0x1c51(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    47cf:	e8 cc dc ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    47d4:	bf 01 00 00 00       	mov    $0x1,%edi
    47d9:	e8 a2 dc ff ff       	call   2480 <exit@plt>
    47de:	66 90                	xchg   %ax,%ax

00000000000047e0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    47e0:	f3 0f 1e fa          	endbr64
    47e4:	41 57                	push   %r15
    47e6:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    47e8:	4c 8d 35 96 18 00 00 	lea    0x1896(%rip),%r14        # 6085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    47ef:	41 55                	push   %r13
    47f1:	49 89 d5             	mov    %rdx,%r13
    47f4:	41 54                	push   %r12
    47f6:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    47f9:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    47fc:	55                   	push   %rbp
    47fd:	53                   	push   %rbx
    47fe:	48 83 ec 18          	sub    $0x18,%rsp
    4802:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    480b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4810:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4812:	49 89 e7             	mov    %rsp,%r15
    4815:	4c 89 fa             	mov    %r15,%rdx
    4818:	e8 43 db ff ff       	call   2360 <strtok_r@plt>
    for (; *str; ++str)
    481d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4821:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4824:	84 db                	test   %bl,%bl
    4826:	74 1d                	je     4845 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4828:	e8 c3 dc ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    482d:	48 89 ea             	mov    %rbp,%rdx
    4830:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4833:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4837:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    483a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    483d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4841:	84 db                	test   %bl,%bl
    4843:	75 eb                	jne    4830 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4845:	4c 89 fa             	mov    %r15,%rdx
    4848:	4c 89 f6             	mov    %r14,%rsi
    484b:	31 ff                	xor    %edi,%edi
    484d:	e8 0e db ff ff       	call   2360 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    4852:	48 8d 35 da 18 00 00 	lea    0x18da(%rip),%rsi        # 6133 <_IO_stdin_used+0x133>
    4859:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    485c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    485f:	e8 2c db ff ff       	call   2390 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    4864:	4c 89 ea             	mov    %r13,%rdx
    4867:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    486a:	85 c0                	test   %eax,%eax
    486c:	75 2a                	jne    4898 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    486e:	48 89 df             	mov    %rbx,%rdi
    4871:	e8 3a fd ff ff       	call   45b0 <handle_get_method>
}
    4876:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    487b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4884:	75 20                	jne    48a6 <handle_http_method+0xc6>
    4886:	48 83 c4 18          	add    $0x18,%rsp
    488a:	5b                   	pop    %rbx
    488b:	5d                   	pop    %rbp
    488c:	41 5c                	pop    %r12
    488e:	41 5d                	pop    %r13
    4890:	41 5e                	pop    %r14
    4892:	41 5f                	pop    %r15
    4894:	c3                   	ret
    4895:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    4898:	48 8b 3d 79 47 00 00 	mov    0x4779(%rip),%rdi        # 9018 <unimplemented_content>
    489f:	e8 9c fb ff ff       	call   4440 <_send_static_string_content>
}
    48a4:	eb d0                	jmp    4876 <handle_http_method+0x96>
    48a6:	e8 65 da ff ff       	call   2310 <__stack_chk_fail@plt>
    48ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000048b0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    48b0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    48b4:	85 d2                	test   %edx,%edx
    48b6:	7e 38                	jle    48f0 <get_line+0x40>
    48b8:	48 63 d2             	movslq %edx,%rdx
    48bb:	48 83 c7 01          	add    $0x1,%rdi
    48bf:	48 01 f2             	add    %rsi,%rdx
    48c2:	eb 11                	jmp    48d5 <get_line+0x25>
    48c4:	0f 1f 40 00          	nopl   0x0(%rax)
    48c8:	48 83 c6 01          	add    $0x1,%rsi
    48cc:	48 83 c7 01          	add    $0x1,%rdi
    48d0:	48 39 d6             	cmp    %rdx,%rsi
    48d3:	74 1b                	je     48f0 <get_line+0x40>
        dest[i] = src[i];
    48d5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    48d9:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    48db:	3c 0d                	cmp    $0xd,%al
    48dd:	75 e9                	jne    48c8 <get_line+0x18>
    48df:	80 3f 0a             	cmpb   $0xa,(%rdi)
    48e2:	75 e4                	jne    48c8 <get_line+0x18>
            dest[i] = '\0';
    48e4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    48e7:	31 c0                	xor    %eax,%eax
    48e9:	c3                   	ret
    48ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    48f0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    48f5:	c3                   	ret
    48f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004900 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4900:	f3 0f 1e fa          	endbr64
    4904:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    490b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    490f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4918:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4920:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4922:	49 89 e2             	mov    %rsp,%r10
    4925:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    492d:	4c 89 d0             	mov    %r10,%rax
    4930:	eb 13                	jmp    4945 <handle_client_request+0x45>
    4932:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4938:	48 83 c0 01          	add    $0x1,%rax
    493c:	48 83 c1 01          	add    $0x1,%rcx
    4940:	4c 39 c8             	cmp    %r9,%rax
    4943:	74 4b                	je     4990 <handle_client_request+0x90>
        dest[i] = src[i];
    4945:	44 0f b6 01          	movzbl (%rcx),%r8d
    4949:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    494c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4950:	75 e6                	jne    4938 <handle_client_request+0x38>
    4952:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4956:	75 e0                	jne    4938 <handle_client_request+0x38>
            dest[i] = '\0';
    4958:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    495b:	8b 47 08             	mov    0x8(%rdi),%eax
    495e:	48 89 f2             	mov    %rsi,%rdx
    4961:	4c 89 d7             	mov    %r10,%rdi
    4964:	89 c6                	mov    %eax,%esi
    4966:	e8 75 fe ff ff       	call   47e0 <handle_http_method>
}
    496b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4973:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    497c:	75 39                	jne    49b7 <handle_client_request+0xb7>
    497e:	31 c0                	xor    %eax,%eax
    4980:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4987:	c3                   	ret
    4988:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4990:	48 8b 0d 89 46 00 00 	mov    0x4689(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4997:	ba 12 00 00 00       	mov    $0x12,%edx
    499c:	be 01 00 00 00       	mov    $0x1,%esi
    49a1:	48 8d 3d 8f 17 00 00 	lea    0x178f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    49a8:	e8 f3 da ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    49ad:	bf 01 00 00 00       	mov    $0x1,%edi
    49b2:	e8 c9 da ff ff       	call   2480 <exit@plt>
}
    49b7:	e8 54 d9 ff ff       	call   2310 <__stack_chk_fail@plt>
    49bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000049c0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    49c0:	f3 0f 1e fa          	endbr64
    49c4:	55                   	push   %rbp
    49c5:	53                   	push   %rbx
    49c6:	48 89 cb             	mov    %rcx,%rbx
    49c9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    49cd:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    49d0:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    49d3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    49d9:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    49dc:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    49df:	f6 c1 02             	test   $0x2,%cl
    49e2:	74 00                	je     49e4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    49e4:	41 89 c0             	mov    %eax,%r8d
    49e7:	45 29 c8             	sub    %r9d,%r8d
    49ea:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    49ee:	0f 82 78 db ff ff    	jb     256c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    49f4:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    49f7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    49fa:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    49fd:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4a00:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4a03:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4a07:	d3 e5                	shl    %cl,%ebp
    4a09:	48 c1 e5 06          	shl    $0x6,%rbp
    4a0d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4a11:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4a14:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4a19:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4a20:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4a24:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4a28:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4a30:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4a38:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4a3c:	e8 af d9 ff ff       	call   23f0 <malloc@plt>
  io_uring_submit(ring);
    4a41:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4a44:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4a4a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4a4e:	48 83 c4 08          	add    $0x8,%rsp
    4a52:	5b                   	pop    %rbx
    4a53:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4a54:	e9 c7 d8 ff ff       	jmp    2320 <io_uring_submit@plt>
    4a59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004a60 <io_thread>:
void* io_thread(void *arg) {
    4a60:	f3 0f 1e fa          	endbr64
    4a64:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4a66:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    4a68:	41 56                	push   %r14
    4a6a:	41 55                	push   %r13
    4a6c:	41 54                	push   %r12
    4a6e:	55                   	push   %rbp
    4a6f:	48 89 fd             	mov    %rdi,%rbp
    4a72:	53                   	push   %rbx
    4a73:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    4a7a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4a83:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4a8b:	48 8b 47 40          	mov    0x40(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4a8f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4a94:	bf 00 01 00 00       	mov    $0x100,%edi
    4a99:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4a9c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4aa0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4aa5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4aaa:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4aaf:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4ab4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4abc:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4ac1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4ac9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4ace:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4ad6:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4adb:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4ae3:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4ae8:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4af0:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4af5:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4afd:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4b05:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4b0d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4b15:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4b1d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4b25:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4b2d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4b35:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4b3d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4b45:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4b4d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4b54:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4b5c:	e8 6f d8 ff ff       	call   23d0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4b61:	48 8b 7d 40          	mov    0x40(%rbp),%rdi
    4b65:	31 f6                	xor    %esi,%esi
    4b67:	e8 54 d9 ff ff       	call   24c0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4b6c:	31 d2                	xor    %edx,%edx
    4b6e:	be 01 00 00 00       	mov    $0x1,%esi
    4b73:	bf 02 00 00 00       	mov    $0x2,%edi
    4b78:	e8 93 d9 ff ff       	call   2510 <socket@plt>
  if (sock == -1)
    4b7d:	83 f8 ff             	cmp    $0xffffffff,%eax
    4b80:	0f 84 28 da ff ff    	je     25ae <io_thread.cold+0x38>
  if (setsockopt(sock,
    4b86:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4b8b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4b91:	89 c7                	mov    %eax,%edi
    4b93:	41 89 c4             	mov    %eax,%r12d
    4b96:	ba 02 00 00 00       	mov    $0x2,%edx
    4b9b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    4ba0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    4ba8:	e8 33 d7 ff ff       	call   22e0 <setsockopt@plt>
    4bad:	85 c0                	test   %eax,%eax
    4baf:	0f 88 cd d9 ff ff    	js     2582 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    4bb5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4bba:	ba 10 00 00 00       	mov    $0x10,%edx
    4bbf:	44 89 e7             	mov    %r12d,%edi
    4bc2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4bcb:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4bd3:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    4bdb:	e8 60 d8 ff ff       	call   2440 <bind@plt>
    4be0:	85 c0                	test   %eax,%eax
    4be2:	0f 88 d2 d9 ff ff    	js     25ba <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4be8:	be 0a 00 00 00       	mov    $0xa,%esi
    4bed:	44 89 e7             	mov    %r12d,%edi
    4bf0:	e8 0b d8 ff ff       	call   2400 <listen@plt>
    4bf5:	85 c0                	test   %eax,%eax
    4bf7:	0f 88 91 d9 ff ff    	js     258e <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4bfd:	ba db 18 00 00       	mov    $0x18db,%edx
    4c02:	48 8d 35 73 15 00 00 	lea    0x1573(%rip),%rsi        # 617c <_IO_stdin_used+0x17c>
    4c09:	bf 01 00 00 00       	mov    $0x1,%edi
    4c0e:	31 c0                	xor    %eax,%eax
    4c10:	e8 1b d8 ff ff       	call   2430 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4c15:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4c1a:	48 89 d9             	mov    %rbx,%rcx
    4c1d:	44 89 e7             	mov    %r12d,%edi
    4c20:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4c25:	48 89 c6             	mov    %rax,%rsi
    4c28:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4c2d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    4c32:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4c3a:	e8 81 fd ff ff       	call   49c0 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4c3f:	bf 01 00 00 00       	mov    $0x1,%edi
    4c44:	be 10 00 00 00       	mov    $0x10,%esi
    4c49:	e8 32 d7 ff ff       	call   2380 <calloc@plt>
    void *buf = malloc(size);
    4c4e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4c53:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    4c56:	e8 95 d7 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    4c5b:	48 85 c0             	test   %rax,%rax
    4c5e:	0f 84 ae 04 00 00    	je     5112 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    4c64:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4c68:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4c6f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    4c76:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4c7e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4c81:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4c86:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4c88:	f6 c1 02             	test   $0x2,%cl
    4c8b:	0f 85 0f 04 00 00    	jne    50a0 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    4c91:	89 d0                	mov    %edx,%eax
    4c93:	29 f0                	sub    %esi,%eax
    4c95:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4c9c:	0f 82 02 d9 ff ff    	jb     25a4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    4ca2:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4ca5:	48 8d 75 48          	lea    0x48(%rbp),%rsi
	sqe->addr3 = 0;
    4ca9:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    4cad:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4cb0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4cb7:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4cba:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4cc1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4cc8:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4cca:	8b 55 48             	mov    0x48(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4ccd:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4cd2:	48 c1 e0 06          	shl    $0x6,%rax
    4cd6:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4cde:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4ce4:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4ce7:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4cef:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4cf3:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4cfb:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4d03:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4d07:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    4d0b:	e8 10 d6 ff ff       	call   2320 <io_uring_submit@plt>
  while (data->running == 1) {
    4d10:	83 7d 2c 01          	cmpl   $0x1,0x2c(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4d14:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4d19:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4d21:	0f 85 d7 01 00 00    	jne    4efe <io_thread+0x49e>
    4d27:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4d2c:	4d 89 ce             	mov    %r9,%r14
    4d2f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4d34:	0f 1f 40 00          	nopl   0x0(%rax)
    4d38:	48 8d 3d 53 14 00 00 	lea    0x1453(%rip),%rdi        # 6192 <_IO_stdin_used+0x192>
    4d3f:	e8 8c d5 ff ff       	call   22d0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    4d44:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    4d4b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    4d52:	c1 e9 0b             	shr    $0xb,%ecx
    4d55:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    4d58:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4d60:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    4d62:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    4d6a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    4d6c:	39 d0                	cmp    %edx,%eax
    4d6e:	74 36                	je     4da6 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    4d70:	89 f8                	mov    %edi,%eax
    4d72:	21 d0                	and    %edx,%eax
    4d74:	d3 e0                	shl    %cl,%eax
    4d76:	48 c1 e0 04          	shl    $0x4,%rax
    4d7a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    4d82:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    4d8a:	0f 85 a8 01 00 00    	jne    4f38 <io_thread+0x4d8>
    4d90:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4d94:	0f 85 0e 03 00 00    	jne    50a8 <io_thread+0x648>
			if (cqe->res < 0)
    4d9a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4d9d:	83 c2 01             	add    $0x1,%edx
    4da0:	89 16                	mov    %edx,(%rsi)
			if (!err)
    4da2:	85 c0                	test   %eax,%eax
    4da4:	79 b2                	jns    4d58 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    4da6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    4daf:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4db0:	45 31 c0             	xor    %r8d,%r8d
    4db3:	31 d2                	xor    %edx,%edx
    4db5:	b9 01 00 00 00       	mov    $0x1,%ecx
    4dba:	4c 89 f6             	mov    %r14,%rsi
    4dbd:	48 89 df             	mov    %rbx,%rdi
    4dc0:	e8 5b d6 ff ff       	call   2420 <__io_uring_get_cqe@plt>
    4dc5:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    4dc8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4dcd:	48 83 38 01          	cmpq   $0x1,(%rax)
    4dd1:	0f 84 e1 02 00 00    	je     50b8 <io_thread+0x658>
    4dd7:	48 8d 3d da 13 00 00 	lea    0x13da(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4dde:	e8 ed d4 ff ff       	call   22d0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4de3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4de8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    4deb:	45 85 ff             	test   %r15d,%r15d
    4dee:	0f 88 82 d7 ff ff    	js     2576 <io_thread.cold>
      if (cqe->res < 0) {
    4df4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    4df7:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    4dfb:	85 c0                	test   %eax,%eax
    4dfd:	0f 88 d5 02 00 00    	js     50d8 <io_thread+0x678>
      switch (req->event_type) {
    4e03:	41 83 f8 01          	cmp    $0x1,%r8d
    4e07:	0f 84 7b 01 00 00    	je     4f88 <io_thread+0x528>
    4e0d:	41 83 f8 02          	cmp    $0x2,%r8d
    4e11:	0f 84 a1 01 00 00    	je     4fb8 <io_thread+0x558>
    4e17:	45 85 c0             	test   %r8d,%r8d
    4e1a:	0f 85 50 01 00 00    	jne    4f70 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4e20:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    4e25:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    4e2a:	48 89 d9             	mov    %rbx,%rcx
    4e2d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    4e31:	e8 8a fb ff ff       	call   49c0 <add_accept_request>
              add_read_request(cqe->res, &ring);
    4e36:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4e3b:	48 89 de             	mov    %rbx,%rsi
    4e3e:	8b 78 08             	mov    0x8(%rax),%edi
    4e41:	e8 1a f5 ff ff       	call   4360 <add_read_request>
              free(req);
    4e46:	4c 89 e7             	mov    %r12,%rdi
    4e49:	e8 62 d4 ff ff       	call   22b0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    4e4e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    4e53:	48 85 c0             	test   %rax,%rax
    4e56:	0f 85 14 01 00 00    	jne    4f70 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    4e5c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4e63:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4e6a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4e6d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4e72:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4e74:	f6 c1 02             	test   $0x2,%cl
    4e77:	74 00                	je     4e79 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    4e79:	89 d0                	mov    %edx,%eax
    4e7b:	29 f0                	sub    %esi,%eax
    4e7d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4e84:	0f 82 10 d7 ff ff    	jb     259a <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    4e8a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    4e8d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    4e92:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    4e96:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4e99:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4ea0:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ea3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4eaa:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4eb1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4eb3:	8b 55 48             	mov    0x48(%rbp),%edx
    4eb6:	48 c1 e0 06          	shl    $0x6,%rax
    4eba:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4ec2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4ec8:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4ecb:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4ed3:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4ed7:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4edf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4ee7:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4eeb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    4eef:	e8 2c d4 ff ff       	call   2320 <io_uring_submit@plt>
  while (data->running == 1) {
    4ef4:	83 7d 2c 01          	cmpl   $0x1,0x2c(%rbp)
    4ef8:	0f 84 3a fe ff ff    	je     4d38 <io_thread+0x2d8>
    4efe:	48 8d 3d ec 12 00 00 	lea    0x12ec(%rip),%rdi        # 61f1 <_IO_stdin_used+0x1f1>
    4f05:	e8 c6 d3 ff ff       	call   22d0 <puts@plt>
}
    4f0a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    4f12:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4f1b:	0f 85 18 02 00 00    	jne    5139 <io_thread+0x6d9>
    4f21:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    4f28:	31 c0                	xor    %eax,%eax
    4f2a:	5b                   	pop    %rbx
    4f2b:	5d                   	pop    %rbp
    4f2c:	41 5c                	pop    %r12
    4f2e:	41 5d                	pop    %r13
    4f30:	41 5e                	pop    %r14
    4f32:	41 5f                	pop    %r15
    4f34:	c3                   	ret
    4f35:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    4f38:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    4f3d:	48 85 c0             	test   %rax,%rax
    4f40:	0f 84 6a fe ff ff    	je     4db0 <io_thread+0x350>
      if (cqe->user_data == 1) {
    4f46:	48 83 38 01          	cmpq   $0x1,(%rax)
    4f4a:	0f 84 68 01 00 00    	je     50b8 <io_thread+0x658>
    4f50:	48 8d 3d 61 12 00 00 	lea    0x1261(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4f57:	e8 74 d3 ff ff       	call   22d0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4f5c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4f61:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    4f64:	e9 8b fe ff ff       	jmp    4df4 <io_thread+0x394>
    4f69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4f70:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    4f78:	8b 02                	mov    (%rdx),%eax
    4f7a:	83 c0 01             	add    $0x1,%eax
    4f7d:	89 02                	mov    %eax,(%rdx)
}
    4f7f:	e9 d8 fe ff ff       	jmp    4e5c <io_thread+0x3fc>
    4f84:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    4f88:	85 c0                	test   %eax,%eax
    4f8a:	75 74                	jne    5000 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4f8c:	48 8b 0d 8d 40 00 00 	mov    0x408d(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4f93:	ba 0f 00 00 00       	mov    $0xf,%edx
    4f98:	be 01 00 00 00       	mov    $0x1,%esi
    4f9d:	48 8d 3d 3d 12 00 00 	lea    0x123d(%rip),%rdi        # 61e1 <_IO_stdin_used+0x1e1>
    4fa4:	e8 f7 d4 ff ff       	call   24a0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    4fa9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4fae:	e9 a0 fe ff ff       	jmp    4e53 <io_thread+0x3f3>
    4fb3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    4fb8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    4fbd:	45 31 ff             	xor    %r15d,%r15d
    4fc0:	85 c0                	test   %eax,%eax
    4fc2:	7e 20                	jle    4fe4 <io_thread+0x584>
    4fc4:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    4fc8:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    4fcb:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    4fcf:	48 c1 e0 04          	shl    $0x4,%rax
    4fd3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    4fd8:	e8 d3 d2 ff ff       	call   22b0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    4fdd:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    4fe2:	7f e4                	jg     4fc8 <io_thread+0x568>
              close(req->client_socket);
    4fe4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    4fe9:	e8 62 d3 ff ff       	call   2350 <close@plt>
              free(req);
    4fee:	4c 89 e7             	mov    %r12,%rdi
    4ff1:	e8 ba d2 ff ff       	call   22b0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    4ff6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    4ffb:	e9 53 fe ff ff       	jmp    4e53 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5000:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5005:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    500a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5012:	eb 11                	jmp    5025 <io_thread+0x5c5>
    5014:	0f 1f 40 00          	nopl   0x0(%rax)
    5018:	48 83 c0 01          	add    $0x1,%rax
    501c:	48 83 c2 01          	add    $0x1,%rdx
    5020:	48 39 c6             	cmp    %rax,%rsi
    5023:	74 4b                	je     5070 <io_thread+0x610>
        dest[i] = src[i];
    5025:	0f b6 0a             	movzbl (%rdx),%ecx
    5028:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    502a:	80 f9 0d             	cmp    $0xd,%cl
    502d:	75 e9                	jne    5018 <io_thread+0x5b8>
    502f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5033:	75 e3                	jne    5018 <io_thread+0x5b8>
            dest[i] = '\0';
    5035:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5038:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    503d:	48 89 da             	mov    %rbx,%rdx
    5040:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5045:	e8 96 f7 ff ff       	call   47e0 <handle_http_method>
              free(req->iov[0].iov_base);
    504a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    504f:	e8 5c d2 ff ff       	call   22b0 <free@plt>
              free(req);
    5054:	4c 89 e7             	mov    %r12,%rdi
    5057:	e8 54 d2 ff ff       	call   22b0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    505c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5061:	e9 ed fd ff ff       	jmp    4e53 <io_thread+0x3f3>
    5066:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5070:	48 8b 0d a9 3f 00 00 	mov    0x3fa9(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    5077:	ba 12 00 00 00       	mov    $0x12,%edx
    507c:	be 01 00 00 00       	mov    $0x1,%esi
    5081:	48 8d 3d af 10 00 00 	lea    0x10af(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    5088:	e8 13 d4 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    508d:	bf 01 00 00 00       	mov    $0x1,%edi
    5092:	e8 e9 d3 ff ff       	call   2480 <exit@plt>
    5097:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    50a0:	e9 ec fb ff ff       	jmp    4c91 <io_thread+0x231>
    50a5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    50a8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    50ad:	e9 94 fe ff ff       	jmp    4f46 <io_thread+0x4e6>
    50b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    50b8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    50c0:	48 8d 3d dd 10 00 00 	lea    0x10dd(%rip),%rdi        # 61a4 <_IO_stdin_used+0x1a4>
    50c7:	8b 02                	mov    (%rdx),%eax
    50c9:	83 c0 01             	add    $0x1,%eax
    50cc:	89 02                	mov    %eax,(%rdx)
    50ce:	e8 fd d1 ff ff       	call   22d0 <puts@plt>
    50d3:	e9 26 fe ff ff       	jmp    4efe <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    50d8:	f7 d8                	neg    %eax
    50da:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    50df:	89 c7                	mov    %eax,%edi
    50e1:	e8 fa d3 ff ff       	call   24e0 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    50e6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    50eb:	be 01 00 00 00       	mov    $0x1,%esi
    50f0:	48 8b 3d 29 3f 00 00 	mov    0x3f29(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    50f7:	48 89 c1             	mov    %rax,%rcx
    50fa:	48 8d 15 4f 13 00 00 	lea    0x134f(%rip),%rdx        # 6450 <_IO_stdin_used+0x450>
    5101:	31 c0                	xor    %eax,%eax
    5103:	e8 a8 d3 ff ff       	call   24b0 <__fprintf_chk@plt>
          exit(1);
    5108:	bf 01 00 00 00       	mov    $0x1,%edi
    510d:	e8 6e d3 ff ff       	call   2480 <exit@plt>
    5112:	48 8b 0d 07 3f 00 00 	mov    0x3f07(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    5119:	ba 28 00 00 00       	mov    $0x28,%edx
    511e:	be 01 00 00 00       	mov    $0x1,%esi
    5123:	48 8d 3d f6 12 00 00 	lea    0x12f6(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    512a:	e8 71 d3 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    512f:	bf 01 00 00 00       	mov    $0x1,%edi
    5134:	e8 47 d3 ff ff       	call   2480 <exit@plt>
}
    5139:	e8 d2 d1 ff ff       	call   2310 <__stack_chk_fail@plt>
    513e:	66 90                	xchg   %ax,%ax

0000000000005140 <receive>:
int receive(struct BarrierTask *data) {
    5140:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    5144:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    514a:	85 c0                	test   %eax,%eax
    514c:	0f 8e ed 00 00 00    	jle    523f <receive+0xff>
int receive(struct BarrierTask *data) {
    5152:	41 54                	push   %r12
    5154:	4c 63 e0             	movslq %eax,%r12
    5157:	48 89 fa             	mov    %rdi,%rdx
    515a:	55                   	push   %rbp
    515b:	49 c1 e4 05          	shl    $0x5,%r12
    515f:	53                   	push   %rbx
    5160:	48 8b b7 28 02 00 00 	mov    0x228(%rdi),%rsi
    5167:	49 01 f4             	add    %rsi,%r12
    516a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    5170:	48 8b 2e             	mov    (%rsi),%rbp
    for (int x = 0 ; x < me->messages_count ; x++) {
    5173:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    517a:	48 85 ff             	test   %rdi,%rdi
    517d:	0f 8e 9d 00 00 00    	jle    5220 <receive+0xe0>
      data->sends++;
    5183:	48 8b 8a 30 02 00 00 	mov    0x230(%rdx),%rcx
    518a:	4c 8b 45 00          	mov    0x0(%rbp),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    518e:	4c 63 1a             	movslq (%rdx),%r11
    5191:	49 89 c9             	mov    %rcx,%r9
    5194:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5198:	49 f7 d9             	neg    %r9
    519b:	48 01 c7             	add    %rax,%rdi
    519e:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    51a2:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
      data->mailboxes[n].received++;
    51a9:	4c 8b 46 18          	mov    0x18(%rsi),%r8
      data->n++;
    51ad:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    51b0:	49 29 c8             	sub    %rcx,%r8
    51b3:	eb 0c                	jmp    51c1 <receive+0x81>
    51b5:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    51b8:	48 83 c0 01          	add    $0x1,%rax
    51bc:	48 39 c7             	cmp    %rax,%rdi
    51bf:	74 5f                	je     5220 <receive+0xe0>
      data->n++;
    51c1:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    51c5:	48 89 82 30 02 00 00 	mov    %rax,0x230(%rdx)
      data->n++;
    51cc:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
      data->mailboxes[n].received++;
    51d3:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    51d7:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    51db:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    51e0:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    51e4:	75 d2                	jne    51b8 <receive+0x78>
    51e6:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    51ed:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    51f1:	75 c5                	jne    51b8 <receive+0x78>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    51f3:	bf 01 00 00 00       	mov    $0x1,%edi
    51f8:	b9 01 00 00 00       	mov    $0x1,%ecx
    51fd:	ba 01 00 00 00       	mov    $0x1,%edx
    5202:	31 c0                	xor    %eax,%eax
    5204:	48 8d 35 6d 12 00 00 	lea    0x126d(%rip),%rsi        # 6478 <_IO_stdin_used+0x478>
    520b:	e8 20 d2 ff ff       	call   2430 <__printf_chk@plt>
        exit(1);
    5210:	bf 01 00 00 00       	mov    $0x1,%edi
    5215:	e8 66 d2 ff ff       	call   2480 <exit@plt>
    521a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    me->messages_count = 0;
    5220:	48 c7 85 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rbp)
  for (int n = 0 ; n < data->thread_count; n++) {
    522b:	48 83 c6 20          	add    $0x20,%rsi
    522f:	49 39 f4             	cmp    %rsi,%r12
    5232:	0f 85 38 ff ff ff    	jne    5170 <receive+0x30>
}
    5238:	5b                   	pop    %rbx
    5239:	31 c0                	xor    %eax,%eax
    523b:	5d                   	pop    %rbp
    523c:	41 5c                	pop    %r12
    523e:	c3                   	ret
    523f:	31 c0                	xor    %eax,%eax
    5241:	c3                   	ret
    5242:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    524d:	0f 1f 00             	nopl   (%rax)

0000000000005250 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    5250:	f3 0f 1e fa          	endbr64
    5254:	41 57                	push   %r15
    5256:	41 56                	push   %r14
    5258:	41 55                	push   %r13
    525a:	41 54                	push   %r12
    525c:	55                   	push   %rbp
    525d:	53                   	push   %rbx
    525e:	48 89 fb             	mov    %rdi,%rbx
    5261:	48 83 ec 28          	sub    $0x28,%rsp
  if (data->thread_index == data->task_index) {
    5265:	8b 07                	mov    (%rdi),%eax
    5267:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    526d:	0f 84 5d 01 00 00    	je     53d0 <barriered_work+0x180>
    receive(data);
    5273:	e8 c8 fe ff ff       	call   5140 <receive>
    while (data->scheduled == 1) {
    5278:	83 bb 00 02 00 00 01 	cmpl   $0x1,0x200(%rbx)
    527f:	75 1b                	jne    529c <barriered_work+0x4c>
    5281:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    5288:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    5290:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    5293:	83 bb 00 02 00 00 01 	cmpl   $0x1,0x200(%rbx)
    529a:	74 ec                	je     5288 <barriered_work+0x38>
    if (data->sending == 1) {
    529c:	83 bb 38 02 00 00 01 	cmpl   $0x1,0x238(%rbx)
    52a3:	74 14                	je     52b9 <barriered_work+0x69>
  asm volatile ("mfence" ::: "memory");
    52a5:	0f ae f0             	mfence
}
    52a8:	48 83 c4 28          	add    $0x28,%rsp
    52ac:	31 c0                	xor    %eax,%eax
    52ae:	5b                   	pop    %rbx
    52af:	5d                   	pop    %rbp
    52b0:	41 5c                	pop    %r12
    52b2:	41 5d                	pop    %r13
    52b4:	41 5e                	pop    %r14
    52b6:	41 5f                	pop    %r15
    52b8:	c3                   	ret
        for (int n = 0 ; n < data->thread_count; n++) {
    52b9:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    52bf:	85 c0                	test   %eax,%eax
    52c1:	7e e2                	jle    52a5 <barriered_work+0x55>
          if (n == data->thread_index) { continue; }
    52c3:	8b bb 30 01 00 00    	mov    0x130(%rbx),%edi
    52c9:	4c 63 f8             	movslq %eax,%r15
    52cc:	48 8d 83 40 02 00 00 	lea    0x240(%rbx),%rax
    52d3:	31 d2                	xor    %edx,%edx
    52d5:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    52da:	48 8d 83 48 02 00 00 	lea    0x248(%rbx),%rax
    52e1:	89 7c 24 04          	mov    %edi,0x4(%rsp)
    52e5:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    52ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    52f0:	39 54 24 04          	cmp    %edx,0x4(%rsp)
    52f4:	0f 84 bc 00 00 00    	je     53b6 <barriered_work+0x166>
          struct Data *them = data->mailboxes[n].higher;
    52fa:	49 89 d0             	mov    %rdx,%r8
    52fd:	49 c1 e0 05          	shl    $0x5,%r8
    5301:	4c 03 83 28 02 00 00 	add    0x228(%rbx),%r8
    5308:	4d 8b 48 08          	mov    0x8(%r8),%r9
          for (; them->messages_count < min;) {
    530c:	4d 8b 99 80 00 00 00 	mov    0x80(%r9),%r11
    5313:	49 63 b9 88 00 00 00 	movslq 0x88(%r9),%rdi
    531a:	49 39 fb             	cmp    %rdi,%r11
    531d:	0f 8d 93 00 00 00    	jge    53b6 <barriered_work+0x166>
    5323:	49 89 fa             	mov    %rdi,%r10
    5326:	4c 8b b3 08 01 00 00 	mov    0x108(%rbx),%r14
    532d:	49 8b 68 10          	mov    0x10(%r8),%rbp
    5331:	4d 29 da             	sub    %r11,%r10
            them->messages[them->messages_count++] = data->message; 
    5334:	49 8b 09             	mov    (%r9),%rcx
    5337:	49 8d 42 ff          	lea    -0x1(%r10),%rax
    533b:	48 83 f8 02          	cmp    $0x2,%rax
    533f:	0f 86 83 02 00 00    	jbe    55c8 <barriered_work+0x378>
    5345:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    534d:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    5355:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    5359:	4c 8d 2c 31          	lea    (%rcx,%rsi,1),%r13
    535d:	4c 39 6c 24 08       	cmp    %r13,0x8(%rsp)
    5362:	0f 83 e8 01 00 00    	jae    5550 <barriered_work+0x300>
    5368:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    536d:	4d 39 ec             	cmp    %r13,%r12
    5370:	0f 83 da 01 00 00    	jae    5550 <barriered_work+0x300>
    5376:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    537a:	48 01 ce             	add    %rcx,%rsi
    537d:	0f 1f 00             	nopl   (%rax)
    5380:	48 8b 83 40 02 00 00 	mov    0x240(%rbx),%rax
          for (; them->messages_count < min;) {
    5387:	49 83 c3 08          	add    $0x8,%r11
            them->messages[them->messages_count++] = data->message; 
    538b:	49 89 43 f8          	mov    %rax,-0x8(%r11)
          for (; them->messages_count < min;) {
    538f:	4c 39 de             	cmp    %r11,%rsi
    5392:	75 ec                	jne    5380 <barriered_work+0x130>
    5394:	0f 1f 40 00          	nopl   0x0(%rax)
    5398:	4b 8d 34 16          	lea    (%r14,%r10,1),%rsi
    539c:	4c 01 d5             	add    %r10,%rbp
    539f:	48 89 b3 08 01 00 00 	mov    %rsi,0x108(%rbx)
    53a6:	49 89 68 10          	mov    %rbp,0x10(%r8)
    53aa:	49 89 b9 80 00 00 00 	mov    %rdi,0x80(%r9)
    53b1:	48 89 44 f9 f8       	mov    %rax,-0x8(%rcx,%rdi,8)
        for (int n = 0 ; n < data->thread_count; n++) {
    53b6:	48 83 c2 01          	add    $0x1,%rdx
    53ba:	4c 39 fa             	cmp    %r15,%rdx
    53bd:	0f 85 2d ff ff ff    	jne    52f0 <barriered_work+0xa0>
    53c3:	e9 dd fe ff ff       	jmp    52a5 <barriered_work+0x55>
    53c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      receive(data);
    53d0:	e8 6b fd ff ff       	call   5140 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    53d5:	8b 8b 34 01 00 00    	mov    0x134(%rbx),%ecx
        int t = data->task_index;
    53db:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    53dd:	85 c9                	test   %ecx,%ecx
    53df:	0f 8e 8e 00 00 00    	jle    5473 <barriered_work+0x223>
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    53e5:	48 63 d0             	movslq %eax,%rdx
              int next_task = abs((t + 1) % (data->thread_count));
    53e8:	83 c0 01             	add    $0x1,%eax
    53eb:	4c 63 d9             	movslq %ecx,%r11
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    53ee:	48 8d 2c 92          	lea    (%rdx,%rdx,4),%rbp
              int next_task = abs((t + 1) % (data->thread_count));
    53f2:	99                   	cltd
    53f3:	f7 f9                	idiv   %ecx
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    53f5:	48 c1 e5 07          	shl    $0x7,%rbp
              int next_task = abs((t + 1) % (data->thread_count));
    53f9:	89 d0                	mov    %edx,%eax
    53fb:	f7 d8                	neg    %eax
    53fd:	0f 48 c2             	cmovs  %edx,%eax
    5400:	49 c1 e3 05          	shl    $0x5,%r11
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5404:	31 ff                	xor    %edi,%edi
    5406:	48 98                	cltq
    5408:	4c 8d 0c 80          	lea    (%rax,%rax,4),%r9
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    540c:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5413:	49 c1 e1 07          	shl    $0x7,%r9
    5417:	4c 8b 60 10          	mov    0x10(%rax),%r12
    541b:	49 83 c4 20          	add    $0x20,%r12
    541f:	4d 89 e2             	mov    %r12,%r10
    5422:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    5428:	49 8b 02             	mov    (%r10),%rax
    542b:	4c 89 e2             	mov    %r12,%rdx
    542e:	48 8b 84 28 28 02 00 00 	mov    0x228(%rax,%rbp,1),%rax
    5436:	4d 8d 04 03          	lea    (%r11,%rax,1),%r8
    543a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5440:	48 8b 0a             	mov    (%rdx),%rcx
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    5443:	48 8b 70 08          	mov    0x8(%rax),%rsi
          for (int b = 0; b < data->thread_count ; b++) {
    5447:	48 83 c0 20          	add    $0x20,%rax
    544b:	48 81 c2 98 00 00 00 	add    $0x98,%rdx
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5452:	4a 8b 8c 09 28 02 00 00 	mov    0x228(%rcx,%r9,1),%rcx
    545a:	48 89 34 39          	mov    %rsi,(%rcx,%rdi,1)
          for (int b = 0; b < data->thread_count ; b++) {
    545e:	49 39 c0             	cmp    %rax,%r8
    5461:	75 dd                	jne    5440 <barriered_work+0x1f0>
        for (int y = 0; y < data->thread_count ; y++) {
    5463:	48 83 c7 20          	add    $0x20,%rdi
    5467:	49 81 c2 98 00 00 00 	add    $0x98,%r10
    546e:	4c 39 df             	cmp    %r11,%rdi
    5471:	75 b5                	jne    5428 <barriered_work+0x1d8>
      asm volatile ("mfence" ::: "memory");
    5473:	0f ae f0             	mfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    5476:	48 8b b3 18 02 00 00 	mov    0x218(%rbx),%rsi
    547d:	31 ff                	xor    %edi,%edi
    547f:	48 c1 e6 05          	shl    $0x5,%rsi
    5483:	48 03 b3 08 02 00 00 	add    0x208(%rbx),%rsi
    548a:	e8 61 ce ff ff       	call   22f0 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    548f:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    while (data->scheduled == 1) {
    5496:	83 bb 00 02 00 00 01 	cmpl   $0x1,0x200(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    549d:	48 8b 42 30          	mov    0x30(%rdx),%rax
    54a1:	8b 78 10             	mov    0x10(%rax),%edi
    54a4:	8d 6f 01             	lea    0x1(%rdi),%ebp
    54a7:	89 68 10             	mov    %ebp,0x10(%rax)
    while (data->scheduled == 1) {
    54aa:	74 0b                	je     54b7 <barriered_work+0x267>
    54ac:	eb 65                	jmp    5513 <barriered_work+0x2c3>
    54ae:	66 90                	xchg   %ax,%ax
    if (modcount != data->thread->protected_state->modcount) {
    54b0:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
    54b7:	48 63 83 30 01 00 00 	movslq 0x130(%rbx),%rax
      data->n++;
    54be:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
    54c6:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    54ca:	48 8d 04 48          	lea    (%rax,%rcx,2),%rax
    54ce:	48 8b 4a 10          	mov    0x10(%rdx),%rcx
    54d2:	48 63 13             	movslq (%rbx),%rdx
    54d5:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    54d9:	48 8d 3c 92          	lea    (%rdx,%rdx,4),%rdi
    54dd:	48 c1 e7 07          	shl    $0x7,%rdi
    54e1:	48 03 78 20          	add    0x20(%rax),%rdi
    54e5:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    54eb:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    54ee:	83 bb 00 02 00 00 01 	cmpl   $0x1,0x200(%rbx)
    54f5:	74 b9                	je     54b0 <barriered_work+0x260>
    if (modcount != data->thread->protected_state->modcount) {
    54f7:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    54fe:	48 8b 40 30          	mov    0x30(%rax),%rax
    5502:	3b 68 10             	cmp    0x10(%rax),%ebp
    5505:	74 0c                	je     5513 <barriered_work+0x2c3>
    5507:	48 8d 3d f6 0c 00 00 	lea    0xcf6(%rip),%rdi        # 6204 <_IO_stdin_used+0x204>
    550e:	e8 bd cd ff ff       	call   22d0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5513:	48 8b b3 18 02 00 00 	mov    0x218(%rbx),%rsi
    551a:	31 ff                	xor    %edi,%edi
    551c:	48 c1 e6 05          	shl    $0x5,%rsi
    5520:	48 03 b3 08 02 00 00 	add    0x208(%rbx),%rsi
    5527:	48 83 c6 10          	add    $0x10,%rsi
    552b:	e8 c0 cd ff ff       	call   22f0 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    5530:	48 8b 83 18 02 00 00 	mov    0x218(%rbx),%rax
    5537:	48 83 c0 01          	add    $0x1,%rax
    553b:	48 99                	cqto
    553d:	48 f7 bb 10 02 00 00 	idivq  0x210(%rbx)
    5544:	48 89 93 18 02 00 00 	mov    %rdx,0x218(%rbx)
    554b:	e9 55 fd ff ff       	jmp    52a5 <barriered_work+0x55>
    5550:	48 8b 83 40 02 00 00 	mov    0x240(%rbx),%rax
    5557:	4d 89 d5             	mov    %r10,%r13
    555a:	4c 89 e6             	mov    %r12,%rsi
    555d:	49 d1 ed             	shr    %r13
    5560:	49 c1 e5 04          	shl    $0x4,%r13
    5564:	66 48 0f 6e c0       	movq   %rax,%xmm0
    5569:	4c 89 6c 24 18       	mov    %r13,0x18(%rsp)
    556e:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    5572:	4d 01 e5             	add    %r12,%r13
    5575:	f6 44 24 18 10       	testb  $0x10,0x18(%rsp)
    557a:	74 14                	je     5590 <barriered_work+0x340>
            them->messages[them->messages_count++] = data->message; 
    557c:	48 83 c6 10          	add    $0x10,%rsi
    5580:	41 0f 11 04 24       	movups %xmm0,(%r12)
          for (; them->messages_count < min;) {
    5585:	49 39 f5             	cmp    %rsi,%r13
    5588:	74 16                	je     55a0 <barriered_work+0x350>
    558a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
    5590:	0f 11 06             	movups %xmm0,(%rsi)
    5593:	48 83 c6 20          	add    $0x20,%rsi
    5597:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
          for (; them->messages_count < min;) {
    559b:	49 39 f5             	cmp    %rsi,%r13
    559e:	75 f0                	jne    5590 <barriered_work+0x340>
    55a0:	4c 89 d6             	mov    %r10,%rsi
    55a3:	48 83 e6 fe          	and    $0xfffffffffffffffe,%rsi
    55a7:	4c 01 de             	add    %r11,%rsi
    55aa:	41 f6 c2 01          	test   $0x1,%r10b
    55ae:	0f 84 e4 fd ff ff    	je     5398 <barriered_work+0x148>
            them->messages[them->messages_count++] = data->message; 
    55b4:	48 8b 83 40 02 00 00 	mov    0x240(%rbx),%rax
    55bb:	48 89 04 f1          	mov    %rax,(%rcx,%rsi,8)
          for (; them->messages_count < min;) {
    55bf:	e9 d4 fd ff ff       	jmp    5398 <barriered_work+0x148>
    55c4:	0f 1f 40 00          	nopl   0x0(%rax)
    55c8:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    55d0:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    55d8:	e9 99 fd ff ff       	jmp    5376 <barriered_work+0x126>
    55dd:	0f 1f 00             	nopl   (%rax)

00000000000055e0 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    55e0:	f3 0f 1e fa          	endbr64
    55e4:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    55e8:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    55ef:	48 8b 40 38          	mov    0x38(%rax),%rax
    55f3:	48 63 10             	movslq (%rax),%rdx
    55f6:	85 d2                	test   %edx,%edx
    55f8:	7e 2c                	jle    5626 <barriered_work_ingest+0x46>
    55fa:	48 8b 40 08          	mov    0x8(%rax),%rax
    55fe:	48 c1 e2 04          	shl    $0x4,%rdx
    5602:	48 01 c2             	add    %rax,%rdx
    5605:	0f 1f 00             	nopl   (%rax)
    if (data->thread->buffers->buffer[x].available == 1) {
    5608:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    560c:	75 0f                	jne    561d <barriered_work_ingest+0x3d>
      data->ingest_count++;
    560e:	48 83 87 20 02 00 00 01 	addq   $0x1,0x220(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    5616:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    561d:	48 83 c0 10          	add    $0x10,%rax
    5621:	48 39 d0             	cmp    %rdx,%rax
    5624:	75 e2                	jne    5608 <barriered_work_ingest+0x28>
  asm volatile ("mfence" ::: "memory");
    5626:	0f ae f0             	mfence
  barriered_work(data);
    5629:	e8 22 fc ff ff       	call   5250 <barriered_work>
}
    562e:	31 c0                	xor    %eax,%eax
    5630:	48 83 c4 08          	add    $0x8,%rsp
    5634:	c3                   	ret
    5635:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005640 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    5640:	f3 0f 1e fa          	endbr64
}
    5644:	31 c0                	xor    %eax,%eax
    5646:	c3                   	ret
    5647:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005650 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    5650:	f3 0f 1e fa          	endbr64
    5654:	31 c0                	xor    %eax,%eax
    5656:	c3                   	ret
    5657:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005660 <after>:
int after(struct timespec left, struct timespec right) {
    5660:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    5664:	31 c0                	xor    %eax,%eax
    5666:	48 39 d7             	cmp    %rdx,%rdi
    5669:	7e 08                	jle    5673 <after+0x13>
    566b:	31 c0                	xor    %eax,%eax
    566d:	48 39 ce             	cmp    %rcx,%rsi
    5670:	0f 9f c0             	setg   %al
}
    5673:	c3                   	ret
    5674:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    567f:	90                   	nop

0000000000005680 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5680:	f3 0f 1e fa          	endbr64
    5684:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5689:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    568e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5690:	48 39 d7             	cmp    %rdx,%rdi
    5693:	7f 18                	jg     56ad <within+0x2d>
    5695:	4d 39 d8             	cmp    %r11,%r8
    5698:	0f 9e c2             	setle  %dl
    569b:	48 39 ce             	cmp    %rcx,%rsi
    569e:	0f 9e c0             	setle  %al
    56a1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    56a3:	31 c0                	xor    %eax,%eax
    56a5:	4d 39 d1             	cmp    %r10,%r9
    56a8:	0f 9e c0             	setle  %al
    56ab:	21 d0                	and    %edx,%eax
}
    56ad:	c3                   	ret
    56ae:	66 90                	xchg   %ax,%ax

00000000000056b0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    56b0:	f3 0f 1e fa          	endbr64
    56b4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    56b9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    56be:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    56c3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    56c8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    56cd:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    56d2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    56d7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    56dc:	48 39 fe             	cmp    %rdi,%rsi
    56df:	7d 2f                	jge    5710 <overlap+0x60>
    56e1:	48 39 ca             	cmp    %rcx,%rdx
    56e4:	7d 62                	jge    5748 <overlap+0x98>
    56e6:	4d 39 da             	cmp    %r11,%r10
    56e9:	7d 0e                	jge    56f9 <overlap+0x49>
    return 1;
    56eb:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    56f0:	4d 39 c1             	cmp    %r8,%r9
    56f3:	0f 8c 7f 00 00 00    	jl     5778 <overlap+0xc8>
  return 0;
    56f9:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    56fb:	4d 39 c1             	cmp    %r8,%r9
    56fe:	7f 4c                	jg     574c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5700:	31 c0                	xor    %eax,%eax
    5702:	4d 39 da             	cmp    %r11,%r10
    5705:	0f 9e c0             	setle  %al
    5708:	c3                   	ret
    5709:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    5710:	7e 4e                	jle    5760 <overlap+0xb0>
    5712:	48 39 ca             	cmp    %rcx,%rdx
    5715:	7f 39                	jg     5750 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5717:	75 31                	jne    574a <overlap+0x9a>
    5719:	4d 39 c1             	cmp    %r8,%r9
    571c:	7c 2c                	jl     574a <overlap+0x9a>
    return 1;
    571e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5723:	4d 39 da             	cmp    %r11,%r10
    5726:	7d 24                	jge    574c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5728:	48 39 ca             	cmp    %rcx,%rdx
    572b:	0f 94 c2             	sete   %dl
    572e:	48 39 fe             	cmp    %rdi,%rsi
    5731:	0f 94 c0             	sete   %al
    5734:	21 c2                	and    %eax,%edx
    5736:	31 c0                	xor    %eax,%eax
    5738:	4d 39 c1             	cmp    %r8,%r9
    573b:	0f 94 c0             	sete   %al
    573e:	21 d0                	and    %edx,%eax
    5740:	c3                   	ret
    5741:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5748:	74 af                	je     56f9 <overlap+0x49>
  return 0;
    574a:	31 c0                	xor    %eax,%eax
}
    574c:	c3                   	ret
    574d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    5750:	4d 39 da             	cmp    %r11,%r10
    5753:	7e c4                	jle    5719 <overlap+0x69>
    return 1;
    5755:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    575a:	4d 39 c1             	cmp    %r8,%r9
    575d:	7e ba                	jle    5719 <overlap+0x69>
    575f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5760:	48 39 ca             	cmp    %rcx,%rdx
    5763:	7c 94                	jl     56f9 <overlap+0x49>
    5765:	4d 39 c1             	cmp    %r8,%r9
    5768:	7d b4                	jge    571e <overlap+0x6e>
    576a:	48 39 ca             	cmp    %rcx,%rdx
    576d:	74 91                	je     5700 <overlap+0x50>
    576f:	eb d9                	jmp    574a <overlap+0x9a>
    5771:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5778:	c3                   	ret
    5779:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005780 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5780:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5784:	85 f6                	test   %esi,%esi
    5786:	0f 8e 49 03 00 00    	jle    5ad5 <verify+0x355>
int verify(struct KernelThread *thread_data, int thread_count) {
    578c:	41 57                	push   %r15
    578e:	41 89 f7             	mov    %esi,%r15d
    5791:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    5793:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    5796:	41 55                	push   %r13
    5798:	41 54                	push   %r12
    579a:	55                   	push   %rbp
    579b:	53                   	push   %rbx
    579c:	48 8d 5f 20          	lea    0x20(%rdi),%rbx
    57a0:	48 83 ec 48          	sub    $0x48,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    57a4:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    57a9:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    57ae:	45 31 e4             	xor    %r12d,%r12d
    57b1:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
      if (z != x)  {
    57b6:	45 39 e6             	cmp    %r12d,%r14d
    57b9:	0f 84 47 02 00 00    	je     5a06 <verify+0x286>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    57bf:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    57c4:	8b 50 08             	mov    0x8(%rax),%edx
    57c7:	85 d2                	test   %edx,%edx
    57c9:	0f 8e 37 02 00 00    	jle    5a06 <verify+0x286>
    57cf:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
    57d7:	31 ed                	xor    %ebp,%ebp
    57d9:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    57de:	44 89 7c 24 34       	mov    %r15d,0x34(%rsp)
    57e3:	45 89 f7             	mov    %r14d,%r15d
    57e6:	41 89 ee             	mov    %ebp,%r14d
    57e9:	44 89 fa             	mov    %r15d,%edx
    57ec:	48 8d 35 21 0a 00 00 	lea    0xa21(%rip),%rsi        # 6214 <_IO_stdin_used+0x214>
    57f3:	bf 01 00 00 00       	mov    $0x1,%edi
    57f8:	31 c0                	xor    %eax,%eax
    57fa:	e8 31 cc ff ff       	call   2430 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    57ff:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5804:	8b 40 08             	mov    0x8(%rax),%eax
    5807:	85 c0                	test   %eax,%eax
    5809:	0f 8e cf 01 00 00    	jle    59de <verify+0x25e>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    580f:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5814:	44 89 74 24 38       	mov    %r14d,0x38(%rsp)
    5819:	31 db                	xor    %ebx,%ebx
    581b:	44 89 7c 24 3c       	mov    %r15d,0x3c(%rsp)
    5820:	4c 8b 20             	mov    (%rax),%r12
    5823:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5828:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    582d:	48 8d 04 9b          	lea    (%rbx,%rbx,4),%rax
    5831:	4c 8b 3c 24          	mov    (%rsp),%r15
    5835:	48 8d 35 ed 09 00 00 	lea    0x9ed(%rip),%rsi        # 6229 <_IO_stdin_used+0x229>
    583c:	49 89 c6             	mov    %rax,%r14
    583f:	bf 01 00 00 00       	mov    $0x1,%edi
    5844:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5848:	49 c1 e6 07          	shl    $0x7,%r14
    584c:	4b 8b 8c 3c 18 02 00 00 	mov    0x218(%r12,%r15,1),%rcx
    5854:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    5859:	4a 8b 94 30 18 02 00 00 	mov    0x218(%rax,%r14,1),%rdx
    5861:	31 c0                	xor    %eax,%eax
    5863:	e8 c8 cb ff ff       	call   2430 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5868:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    586d:	4c 8b 20             	mov    (%rax),%r12
    5870:	4b 83 bc 3c 18 02 00 00 00 	cmpq   $0x0,0x218(%r12,%r15,1)
    5879:	0f 8e 43 01 00 00    	jle    59c2 <verify+0x242>
    587f:	4c 03 75 00          	add    0x0(%rbp),%r14
    5883:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5888:	ba 01 00 00 00       	mov    $0x1,%edx
    588d:	4d 89 f5             	mov    %r14,%r13
    5890:	4d 8b b5 18 02 00 00 	mov    0x218(%r13),%r14
    5897:	4d 85 f6             	test   %r14,%r14
    589a:	0f 8e 1d 01 00 00    	jle    59bd <verify+0x23d>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    58a0:	48 89 d5             	mov    %rdx,%rbp
    58a3:	48 8b 04 24          	mov    (%rsp),%rax
    58a7:	31 db                	xor    %ebx,%ebx
    58a9:	4d 89 f2             	mov    %r14,%r10
    58ac:	48 c1 e5 05          	shl    $0x5,%rbp
    58b0:	48 83 ed 20          	sub    $0x20,%rbp
    58b4:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    58b8:	49 89 ee             	mov    %rbp,%r14
    58bb:	48 89 dd             	mov    %rbx,%rbp
    58be:	48 89 d3             	mov    %rdx,%rbx
    58c1:	eb 32                	jmp    58f5 <verify+0x175>
    58c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    58c8:	4c 39 c2             	cmp    %r8,%rdx
    58cb:	0f 8d 57 01 00 00    	jge    5a28 <verify+0x2a8>
    58d1:	4c 39 df             	cmp    %r11,%rdi
    58d4:	7e 05                	jle    58db <verify+0x15b>
    58d6:	49 39 c1             	cmp    %rax,%r9
    58d9:	7c 75                	jl     5950 <verify+0x1d0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    58db:	4c 39 df             	cmp    %r11,%rdi
    58de:	0f 8d b3 01 00 00    	jge    5a97 <verify+0x317>
    58e4:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    58e8:	48 83 c5 01          	add    $0x1,%rbp
    58ec:	49 39 ea             	cmp    %rbp,%r10
    58ef:	0f 8e a8 00 00 00    	jle    599d <verify+0x21d>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    58f5:	49 8b 97 08 02 00 00 	mov    0x208(%r15),%rdx
    58fc:	48 89 e8             	mov    %rbp,%rax
    58ff:	48 c1 e0 05          	shl    $0x5,%rax
    5903:	49 03 85 08 02 00 00 	add    0x208(%r13),%rax
    590a:	4c 01 f2             	add    %r14,%rdx
    590d:	48 8b 08             	mov    (%rax),%rcx
    5910:	48 8b 78 10          	mov    0x10(%rax),%rdi
    5914:	48 8b 32             	mov    (%rdx),%rsi
    5917:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    591b:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    591f:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    5923:	48 8b 50 08          	mov    0x8(%rax),%rdx
    5927:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    592b:	48 39 f1             	cmp    %rsi,%rcx
    592e:	7c 98                	jl     58c8 <verify+0x148>
    5930:	0f 8e 4a 01 00 00    	jle    5a80 <verify+0x300>
    5936:	4c 39 c2             	cmp    %r8,%rdx
    5939:	0f 8f f9 00 00 00    	jg     5a38 <verify+0x2b8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    593f:	75 a7                	jne    58e8 <verify+0x168>
    5941:	4c 39 df             	cmp    %r11,%rdi
    5944:	7f a2                	jg     58e8 <verify+0x168>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5946:	49 39 c1             	cmp    %rax,%r9
    5949:	7c 9d                	jl     58e8 <verify+0x168>
    594b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5950:	49 89 c1             	mov    %rax,%r9
    5953:	48 89 f9             	mov    %rdi,%rcx
    5956:	48 89 f2             	mov    %rsi,%rdx
    5959:	bf 01 00 00 00       	mov    $0x1,%edi
    595e:	48 8d 35 3b 0b 00 00 	lea    0xb3b(%rip),%rsi        # 64a0 <_IO_stdin_used+0x4a0>
    5965:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5967:	48 83 c5 01          	add    $0x1,%rbp
    596b:	e8 c0 ca ff ff       	call   2430 <__printf_chk@plt>
    5970:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5975:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    597a:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    597d:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5982:	4d 8b 95 18 02 00 00 	mov    0x218(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5989:	4c 8b 20             	mov    (%rax),%r12
    598c:	48 8b 04 24          	mov    (%rsp),%rax
    5990:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5994:	49 39 ea             	cmp    %rbp,%r10
    5997:	0f 8f 58 ff ff ff    	jg     58f5 <verify+0x175>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    599d:	48 89 da             	mov    %rbx,%rdx
    59a0:	49 3b 9f 18 02 00 00 	cmp    0x218(%r15),%rbx
    59a7:	7d 14                	jge    59bd <verify+0x23d>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    59a9:	4d 8b b5 18 02 00 00 	mov    0x218(%r13),%r14
    59b0:	48 83 c2 01          	add    $0x1,%rdx
    59b4:	4d 85 f6             	test   %r14,%r14
    59b7:	0f 8f e3 fe ff ff    	jg     58a0 <verify+0x120>
    59bd:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    59c2:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    59c7:	48 83 c3 01          	add    $0x1,%rbx
    59cb:	39 58 08             	cmp    %ebx,0x8(%rax)
    59ce:	0f 8f 54 fe ff ff    	jg     5828 <verify+0xa8>
    59d4:	44 8b 74 24 38       	mov    0x38(%rsp),%r14d
    59d9:	44 8b 7c 24 3c       	mov    0x3c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    59de:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    59e3:	48 81 04 24 80 02 00 00 	addq   $0x280,(%rsp)
    59eb:	41 83 c6 01          	add    $0x1,%r14d
    59ef:	44 39 70 08          	cmp    %r14d,0x8(%rax)
    59f3:	0f 8f f0 fd ff ff    	jg     57e9 <verify+0x69>
    59f9:	45 89 fe             	mov    %r15d,%r14d
    59fc:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    5a01:	44 8b 7c 24 34       	mov    0x34(%rsp),%r15d
    for (int z = 0 ; z < thread_count; z++) {
    5a06:	48 81 44 24 08 98 00 00 00 	addq   $0x98,0x8(%rsp)
    5a0f:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    5a14:	41 39 c7             	cmp    %eax,%r15d
    5a17:	0f 84 88 00 00 00    	je     5aa5 <verify+0x325>
    5a1d:	41 89 c4             	mov    %eax,%r12d
    5a20:	e9 91 fd ff ff       	jmp    57b6 <verify+0x36>
    5a25:	0f 1f 00             	nopl   (%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5a28:	0f 85 ba fe ff ff    	jne    58e8 <verify+0x168>
    5a2e:	e9 a8 fe ff ff       	jmp    58db <verify+0x15b>
    5a33:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5a38:	49 39 c1             	cmp    %rax,%r9
    5a3b:	7e 09                	jle    5a46 <verify+0x2c6>
    5a3d:	4c 39 df             	cmp    %r11,%rdi
    5a40:	0f 8c 0a ff ff ff    	jl     5950 <verify+0x1d0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5a46:	4c 39 df             	cmp    %r11,%rdi
    5a49:	0f 8f 99 fe ff ff    	jg     58e8 <verify+0x168>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5a4f:	49 39 c1             	cmp    %rax,%r9
    5a52:	0f 8d f8 fe ff ff    	jge    5950 <verify+0x1d0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5a58:	48 39 f1             	cmp    %rsi,%rcx
    5a5b:	0f 85 87 fe ff ff    	jne    58e8 <verify+0x168>
    5a61:	4c 39 c2             	cmp    %r8,%rdx
    5a64:	0f 85 7e fe ff ff    	jne    58e8 <verify+0x168>
    5a6a:	4c 39 df             	cmp    %r11,%rdi
    5a6d:	0f 84 dd fe ff ff    	je     5950 <verify+0x1d0>
    5a73:	e9 70 fe ff ff       	jmp    58e8 <verify+0x168>
    5a78:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5a80:	4c 39 c2             	cmp    %r8,%rdx
    5a83:	0f 8c 52 fe ff ff    	jl     58db <verify+0x15b>
    5a89:	4c 39 df             	cmp    %r11,%rdi
    5a8c:	7e c1                	jle    5a4f <verify+0x2cf>
    5a8e:	4c 39 c2             	cmp    %r8,%rdx
    5a91:	0f 85 51 fe ff ff    	jne    58e8 <verify+0x168>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5a97:	49 39 c1             	cmp    %rax,%r9
    5a9a:	0f 8f 48 fe ff ff    	jg     58e8 <verify+0x168>
    5aa0:	e9 ab fe ff ff       	jmp    5950 <verify+0x1d0>
  for (int x = 0 ; x < thread_count; x++) {
    5aa5:	48 81 44 24 10 98 00 00 00 	addq   $0x98,0x10(%rsp)
    5aae:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    5ab3:	41 8d 46 01          	lea    0x1(%r14),%eax
    5ab7:	45 39 e6             	cmp    %r12d,%r14d
    5aba:	74 08                	je     5ac4 <verify+0x344>
    5abc:	41 89 c6             	mov    %eax,%r14d
    5abf:	e9 e5 fc ff ff       	jmp    57a9 <verify+0x29>
}
    5ac4:	48 83 c4 48          	add    $0x48,%rsp
    5ac8:	31 c0                	xor    %eax,%eax
    5aca:	5b                   	pop    %rbx
    5acb:	5d                   	pop    %rbp
    5acc:	41 5c                	pop    %r12
    5ace:	41 5d                	pop    %r13
    5ad0:	41 5e                	pop    %r14
    5ad2:	41 5f                	pop    %r15
    5ad4:	c3                   	ret
    5ad5:	31 c0                	xor    %eax,%eax
    5ad7:	c3                   	ret

Disassembly of section .fini:

0000000000005ad8 <_fini>:
    5ad8:	f3 0f 1e fa          	endbr64
    5adc:	48 83 ec 08          	sub    $0x8,%rsp
    5ae0:	48 83 c4 08          	add    $0x8,%rsp
    5ae4:	c3                   	ret
