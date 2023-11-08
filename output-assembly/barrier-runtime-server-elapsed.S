
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
  struct timespec start __attribute__((aligned (128)));
  struct timespec end __attribute__((aligned (128)));
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
    26f8:	be 80 01 00 00       	mov    $0x180,%esi
    26fd:	bf 01 00 00 00       	mov    $0x1,%edi
    2702:	e8 79 fc ff ff       	call   2380 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2707:	be 00 03 00 00       	mov    $0x300,%esi
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
    27c4:	49 89 87 80 00 00 00 	mov    %rax,0x80(%r15)
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    27cb:	e8 b0 fb ff ff       	call   2380 <calloc@plt>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    27d0:	be 00 01 00 00       	mov    $0x100,%esi
    27d5:	bf 64 00 00 00       	mov    $0x64,%edi
    thread_data[x].timestamp_count = 0;
    27da:	66 0f 6f 15 ee 41 00 00 	movdqa 0x41ee(%rip),%xmm2        # 69d0 <_IO_stdin_used+0x9d0>
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    27e2:	49 89 87 00 01 00 00 	mov    %rax,0x100(%r15)
    thread_data[x].timestamp_count = 0;
    27e9:	41 0f 29 97 00 02 00 00 	movaps %xmm2,0x200(%r15)
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    27f1:	e8 8a fb ff ff       	call   2380 <calloc@plt>
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    27f6:	be 80 05 00 00       	mov    $0x580,%esi
    27fb:	bf 07 00 00 00       	mov    $0x7,%edi
    thread_data[x].task_timestamp_count = 0;
    2800:	66 0f 6f 1d c8 41 00 00 	movdqa 0x41c8(%rip),%xmm3        # 69d0 <_IO_stdin_used+0x9d0>
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2808:	49 89 87 10 02 00 00 	mov    %rax,0x210(%r15)
    thread_data[x].task_timestamp_count = 0;
    280f:	41 0f 29 9f 80 02 00 00 	movaps %xmm3,0x280(%r15)
      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2817:	e8 64 fb ff ff       	call   2380 <calloc@plt>
        thread_data[x].tasks[y].sending = 1;
    281c:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    2821:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
      thread_data[x].tasks = barriers;
    2826:	49 89 47 20          	mov    %rax,0x20(%r15)
        thread_data[x].tasks[y].sending = 1;
    282a:	49 89 c7             	mov    %rax,%r15
    282d:	0f 1f 00             	nopl   (%rax)
            thread_data[x].tasks[y].protected = do_protected_write; 
    2830:	4c 63 eb             	movslq %ebx,%r13
    2833:	44 89 74 24 28       	mov    %r14d,0x28(%rsp)
    2838:	4b 8d 44 ad 00       	lea    0x0(%r13,%r13,4),%rax
    283d:	4d 8d 64 45 00       	lea    0x0(%r13,%rax,2),%r12
    2842:	49 c1 e4 07          	shl    $0x7,%r12
        if (x == y) {
    2846:	44 39 f3             	cmp    %r14d,%ebx
    2849:	0f 84 41 0a 00 00    	je     3290 <main+0xcc0>
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
    284f:	be 00 02 00 00       	mov    $0x200,%esi
    2854:	bf 06 00 00 00       	mov    $0x6,%edi
    2859:	e8 22 fb ff ff       	call   2380 <calloc@plt>
        thread_data[x].tasks[y].mailboxes = mailboxes;
    285e:	89 5c 24 18          	mov    %ebx,0x18(%rsp)
    2862:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
    2867:	48 8d a8 00 0c 00 00 	lea    0xc00(%rax),%rbp
    286e:	4b 89 84 27 88 04 00 00 	mov    %rax,0x488(%r15,%r12,1)
        for (int b = 0 ; b < thread_count ; b++) {
    2876:	49 89 c7             	mov    %rax,%r15
    2879:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2880:	be 08 00 00 00       	mov    $0x8,%esi
    2885:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int b = 0 ; b < thread_count ; b++) {
    288a:	49 81 c7 00 02 00 00 	add    $0x200,%r15
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2891:	e8 ea fa ff ff       	call   2380 <calloc@plt>
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2896:	be 08 00 00 00       	mov    $0x8,%esi
    289b:	bf 01 00 00 00       	mov    $0x1,%edi
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    28a0:	49 89 c4             	mov    %rax,%r12
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    28a3:	e8 d8 fa ff ff       	call   2380 <calloc@plt>
          struct Data *data = calloc(2, sizeof(struct Data));
    28a8:	be 00 01 00 00       	mov    $0x100,%esi
    28ad:	bf 02 00 00 00       	mov    $0x2,%edi
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    28b2:	48 89 c3             	mov    %rax,%rbx
          struct Data *data = calloc(2, sizeof(struct Data));
    28b5:	e8 c6 fa ff ff       	call   2380 <calloc@plt>
          data[0].messages_count = 0;
    28ba:	66 0f 6f 05 1e 41 00 00 	movdqa 0x411e(%rip),%xmm0        # 69e0 <_IO_stdin_used+0x9e0>
          mailboxes[b].higher = &data[1];
    28c2:	48 8d b0 00 01 00 00 	lea    0x100(%rax),%rsi
          mailboxes[b].lower = &data[0];
    28c9:	49 89 87 00 fe ff ff 	mov    %rax,-0x200(%r15)
          mailboxes[b].higher = &data[1];
    28d0:	49 89 b7 80 fe ff ff 	mov    %rsi,-0x180(%r15)
          data[0].messages = messages;
    28d7:	4c 89 20             	mov    %r12,(%rax)
          data[1].messages = messages2;
    28da:	48 89 98 00 01 00 00 	mov    %rbx,0x100(%rax)
          data[0].messages_count = 0;
    28e1:	0f 29 80 80 00 00 00 	movaps %xmm0,0x80(%rax)
          data[1].messages_count = 0;
    28e8:	0f 29 80 80 01 00 00 	movaps %xmm0,0x180(%rax)
        for (int b = 0 ; b < thread_count ; b++) {
    28ef:	49 39 ef             	cmp    %rbp,%r15
    28f2:	75 8c                	jne    2880 <main+0x2b0>
        char *message = malloc(sizeof(char) * 256);
    28f4:	be 01 00 00 00       	mov    $0x1,%esi
    28f9:	bf 00 01 00 00       	mov    $0x100,%edi
    28fe:	8b 5c 24 18          	mov    0x18(%rsp),%ebx
    2902:	4c 8b 64 24 20       	mov    0x20(%rsp),%r12
    2907:	e8 74 fa ff ff       	call   2380 <calloc@plt>
        struct Message *messaged = malloc(sizeof(struct Message));
    290c:	bf 18 00 00 00       	mov    $0x18,%edi
        char *message = malloc(sizeof(char) * 256);
    2911:	48 89 c5             	mov    %rax,%rbp
        struct Message *messaged = malloc(sizeof(struct Message));
    2914:	e8 d7 fa ff ff       	call   23f0 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2919:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    291e:	48 89 ef             	mov    %rbp,%rdi
    2921:	41 89 d9             	mov    %ebx,%r9d
    2924:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2929:	48 8d 0d 50 3c 00 00 	lea    0x3c50(%rip),%rcx        # 6580 <_IO_stdin_used+0x580>
    2930:	ba 00 01 00 00       	mov    $0x100,%edx
    2935:	31 c0                	xor    %eax,%eax
    2937:	be 01 00 00 00       	mov    $0x1,%esi
    293c:	e8 bf fb ff ff       	call   2500 <__sprintf_chk@plt>
        messaged->message = message;
    2941:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2946:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    294b:	ba ab aa aa aa       	mov    $0xaaaaaaab,%edx
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2950:	be 00 01 00 00       	mov    $0x100,%esi
    2955:	bf 3f 42 0f 00       	mov    $0xf423f,%edi
        messaged->task_index = y;
    295a:	4d 89 6a 10          	mov    %r13,0x10(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    295e:	44 8d 6b 01          	lea    0x1(%rbx),%r13d
    2962:	4c 8b 78 20          	mov    0x20(%rax),%r15
    2966:	44 89 e8             	mov    %r13d,%eax
    2969:	44 89 e9             	mov    %r13d,%ecx
        messaged->message = message;
    296c:	49 89 2a             	mov    %rbp,(%r10)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    296f:	48 0f af c2          	imul   %rdx,%rax
    2973:	4b 8d 2c 27          	lea    (%r15,%r12,1),%rbp
        messaged->thread_index = x;
    2977:	4d 89 72 08          	mov    %r14,0x8(%r10)
        thread_data[x].tasks[y].message = messaged;
    297b:	4c 89 95 10 05 00 00 	mov    %r10,0x510(%rbp)
        thread_data[x].tasks[y].snapshot_count = 999999;
    2982:	48 c7 85 80 03 00 00 3f 42 0f 00 	movq   $0xf423f,0x380(%rbp)
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    298d:	48 c1 e8 22          	shr    $0x22,%rax
    2991:	8d 04 40             	lea    (%rax,%rax,2),%eax
    2994:	01 c0                	add    %eax,%eax
    2996:	29 c1                	sub    %eax,%ecx
    2998:	89 8d 18 05 00 00    	mov    %ecx,0x518(%rbp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    299e:	e8 dd f9 ff ff       	call   2380 <calloc@plt>
        thread_data[x].tasks[y].thread_index = x;
    29a3:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
        thread_data[x].tasks[y].task_index = y;
    29a7:	89 5d 00             	mov    %ebx,0x0(%rbp)
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    29aa:	48 89 85 08 03 00 00 	mov    %rax,0x308(%rbp)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    29b1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
        thread_data[x].tasks[y].current_snapshot = 0;
    29b6:	48 c7 85 00 04 00 00 00 00 00 00 	movq   $0x0,0x400(%rbp)
        thread_data[x].tasks[y].thread = &thread_data[x]; 
    29c1:	48 89 85 18 02 00 00 	mov    %rax,0x218(%rbp)
        thread_data[x].tasks[y].available = 1;
    29c8:	48 8b 05 29 40 00 00 	mov    0x4029(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
        thread_data[x].tasks[y].thread_index = x;
    29cf:	89 8d 20 02 00 00    	mov    %ecx,0x220(%rbp)
        thread_data[x].tasks[y].available = 1;
    29d5:	48 89 85 80 02 00 00 	mov    %rax,0x280(%rbp)
        thread_data[x].tasks[y].sending = 1;
    29dc:	48 b8 01 00 00 00 06 00 00 00 	movabs $0x600000001,%rax
        thread_data[x].tasks[y].arrived = 0;
    29e6:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        thread_data[x].tasks[y].thread_count = thread_count;
    29f0:	c7 85 24 02 00 00 06 00 00 00 	movl   $0x6,0x224(%rbp)
        thread_data[x].tasks[y].sending = 1;
    29fa:	48 89 85 08 05 00 00 	mov    %rax,0x508(%rbp)
        if (y == barrier_count - 1) {
    2a01:	83 fb 05             	cmp    $0x5,%ebx
    2a04:	0f 84 66 08 00 00    	je     3270 <main+0xca0>
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
    2a0a:	8b 44 24 28          	mov    0x28(%rsp),%eax
    2a0e:	39 c3                	cmp    %eax,%ebx
    2a10:	75 66                	jne    2a78 <main+0x4a8>
    2a12:	8b 5c 24 34          	mov    0x34(%rsp),%ebx
    2a16:	85 db                	test   %ebx,%ebx
    2a18:	7f 5e                	jg     2a78 <main+0x4a8>
    2a1a:	89 ca                	mov    %ecx,%edx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2a1c:	bf 01 00 00 00       	mov    $0x1,%edi
    2a21:	48 8d 35 80 3b 00 00 	lea    0x3b80(%rip),%rsi        # 65a8 <_IO_stdin_used+0x5a8>
    2a28:	31 c0                	xor    %eax,%eax
    2a2a:	e8 01 fa ff ff       	call   2430 <__printf_chk@plt>
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a2f:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    2a34:	48 63 c3             	movslq %ebx,%rax
    2a37:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    2a3c:	48 89 c1             	mov    %rax,%rcx
    2a3f:	48 c1 e0 04          	shl    $0x4,%rax
    2a43:	48 01 f8             	add    %rdi,%rax
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2a46:	4c 8b 7a 20          	mov    0x20(%rdx),%r15
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a4a:	48 89 42 38          	mov    %rax,0x38(%rdx)
            thread_data[x].tasks[y].run = barriered_work_ingest; 
    2a4e:	48 8d 05 0b 2c 00 00 	lea    0x2c0b(%rip),%rax        # 5660 <barriered_work_ingest>
    2a55:	4b 89 84 27 08 02 00 00 	mov    %rax,0x208(%r15,%r12,1)
            thread_data[x].buffers = &buffers[external_thread_index++];
    2a5d:	8d 41 01             	lea    0x1(%rcx),%eax
    2a60:	89 44 24 34          	mov    %eax,0x34(%rsp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2a64:	41 83 fd 07          	cmp    $0x7,%r13d
    2a68:	74 22                	je     2a8c <main+0x4bc>
  int external_thread_index = 0;
    2a6a:	44 89 eb             	mov    %r13d,%ebx
    2a6d:	e9 be fd ff ff       	jmp    2830 <main+0x260>
    2a72:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            thread_data[x].tasks[y].run = barriered_work; 
    2a78:	48 8d 05 21 28 00 00 	lea    0x2821(%rip),%rax        # 52a0 <barriered_work>
    2a7f:	48 89 85 08 02 00 00 	mov    %rax,0x208(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    2a86:	41 83 fd 07          	cmp    $0x7,%r13d
    2a8a:	75 de                	jne    2a6a <main+0x49a>

          }
        }
      }
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    2a8c:	4c 89 f2             	mov    %r14,%rdx
    2a8f:	48 8d 05 5a 09 00 00 	lea    0x95a(%rip),%rax        # 33f0 <barriered_reset>
    2a96:	4d 89 fe             	mov    %r15,%r14
    2a99:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    2a9e:	49 89 86 08 23 00 00 	mov    %rax,0x2308(%r14)
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = thread_count; 
      thread_data[x].tasks[barrier_count].thread_index = x; 
    2aa5:	8b 44 24 08          	mov    0x8(%rsp),%eax
  for (int x = 0 ; x < total_threads ; x++) {
    2aa9:	48 83 c2 01          	add    $0x1,%rdx
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
    2aad:	4d 89 be 18 23 00 00 	mov    %r15,0x2318(%r14)
  for (int x = 0 ; x < total_threads ; x++) {
    2ab4:	49 81 c7 00 03 00 00 	add    $0x300,%r15
      thread_data[x].tasks[barrier_count].thread_index = x; 
    2abb:	41 89 86 20 23 00 00 	mov    %eax,0x2320(%r14)
      thread_data[x].tasks[barrier_count].available = 1; 
    2ac2:	48 8b 05 2f 3f 00 00 	mov    0x3f2f(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
      thread_data[x].tasks[barrier_count].arrived = 0; 
    2ac9:	41 c7 86 80 21 00 00 00 00 00 00 	movl   $0x0,0x2180(%r14)
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    2ad4:	41 c7 86 00 21 00 00 06 00 00 00 	movl   $0x6,0x2100(%r14)
      thread_data[x].tasks[barrier_count].thread_count = thread_count; 
    2adf:	41 c7 86 24 23 00 00 06 00 00 00 	movl   $0x6,0x2324(%r14)
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    2aea:	41 c7 86 0c 26 00 00 06 00 00 00 	movl   $0x6,0x260c(%r14)
      thread_data[x].tasks[barrier_count].available = 1; 
    2af5:	49 89 86 80 23 00 00 	mov    %rax,0x2380(%r14)
  for (int x = 0 ; x < total_threads ; x++) {
    2afc:	48 83 fa 09          	cmp    $0x9,%rdx
    2b00:	0f 85 72 fc ff ff    	jne    2778 <main+0x1a8>
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].threads = thread_data;
    2b06:	4c 8b 44 24 48       	mov    0x48(%rsp),%r8
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2b0b:	be 38 00 00 00       	mov    $0x38,%esi
    2b10:	bf 09 00 00 00       	mov    $0x9,%edi
  thread_data[thread_count].thread_count = thread_count;
  thread_data[thread_count].thread_index = 0;

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
  for (int x = 0 ; x < thread_count ; x++) {
    2b15:	45 31 ed             	xor    %r13d,%r13d
    2b18:	4c 8d 3d 41 09 00 00 	lea    0x941(%rip),%r15        # 3460 <barriered_thread>
    thread_data[n].tasks[0].scheduled = 1;
    2b1f:	49 8b 40 20          	mov    0x20(%r8),%rax
    2b23:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    thread_data[x].threads = thread_data;
    2b28:	4d 89 80 10 15 00 00 	mov    %r8,0x1510(%r8)
    thread_data[x].thread_count = thread_count;
    2b2f:	41 c7 80 18 15 00 00 06 00 00 00 	movl   $0x6,0x1518(%r8)
    thread_data[x].thread_index = x;
    2b3a:	41 c7 80 00 15 00 00 07 00 00 00 	movl   $0x7,0x1500(%r8)
    thread_data[x].task_count = total_barrier_count;
    2b45:	41 c7 80 28 15 00 00 07 00 00 00 	movl   $0x7,0x1528(%r8)
    thread_data[n].tasks[0].scheduled = 1;
    2b50:	c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rax)
    2b5a:	49 8b 80 20 03 00 00 	mov    0x320(%r8),%rax
    2b61:	c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rax)
    2b6b:	49 8b 80 20 06 00 00 	mov    0x620(%r8),%rax
    2b72:	c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rax)
    2b7c:	49 8b 80 20 09 00 00 	mov    0x920(%r8),%rax
    2b83:	c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rax)
    2b8d:	49 8b 80 20 0c 00 00 	mov    0xc20(%r8),%rax
    2b94:	c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rax)
    2b9e:	49 8b 80 20 0f 00 00 	mov    0xf20(%r8),%rax
    2ba5:	c7 80 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rax)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2baf:	e8 cc f7 ff ff       	call   2380 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bb4:	be 38 00 00 00       	mov    $0x38,%esi
    2bb9:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bbe:	48 89 c3             	mov    %rax,%rbx
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bc1:	e8 ba f7 ff ff       	call   2380 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bc6:	be 38 00 00 00       	mov    $0x38,%esi
    2bcb:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bd0:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2bd5:	e8 a6 f7 ff ff       	call   2380 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2bda:	be 08 00 00 00       	mov    $0x8,%esi
    2bdf:	bf 09 00 00 00       	mov    $0x9,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    2be4:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2be9:	e8 92 f7 ff ff       	call   2380 <calloc@plt>
  thread_data[thread_count].task_count = total_barrier_count;
    2bee:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2bf3:	ba 06 00 00 00       	mov    $0x6,%edx
    2bf8:	48 8d 35 f0 36 00 00 	lea    0x36f0(%rip),%rsi        # 62ef <_IO_stdin_used+0x2ef>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    2bff:	49 89 c4             	mov    %rax,%r12
  thread_data[thread_count].task_count = total_barrier_count;
    2c02:	48 8b 05 f7 3d 00 00 	mov    0x3df7(%rip),%rax        # 6a00 <_IO_stdin_used+0xa00>
    2c09:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[thread_count].threads = thread_data;
    2c0e:	4d 89 80 10 12 00 00 	mov    %r8,0x1210(%r8)
    2c15:	4c 89 e5             	mov    %r12,%rbp
  thread_data[thread_count].task_count = total_barrier_count;
    2c18:	49 89 80 28 12 00 00 	mov    %rax,0x1228(%r8)
    2c1f:	31 c0                	xor    %eax,%eax
  thread_data[thread_count].thread_count = thread_count;
    2c21:	41 c7 80 18 12 00 00 06 00 00 00 	movl   $0x6,0x1218(%r8)
  thread_data[thread_count].thread_index = 0;
    2c2c:	49 c7 80 00 12 00 00 00 00 00 00 	movq   $0x0,0x1200(%r8)
    2c37:	e8 f4 f7 ff ff       	call   2430 <__printf_chk@plt>
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
    2c3c:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2c41:	49 8d 7c 24 30       	lea    0x30(%r12),%rdi
    2c46:	45 89 ec             	mov    %r13d,%r12d
    2c49:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
    2c50:	48 8d 15 a9 0b 00 00 	lea    0xba9(%rip),%rdx        # 3800 <timer_thread>
    2c57:	49 89 ed             	mov    %rbp,%r13
    2c5a:	49 8d 88 00 12 00 00 	lea    0x1200(%r8),%rcx
    2c61:	e8 ea f7 ff ff       	call   2450 <pthread_create@plt>
    2c66:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    2c6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    thread_data[x].type = WORKER;
    2c70:	41 c7 46 04 01 00 00 00 	movl   $0x1,0x4(%r14)
    2c78:	44 89 e2             	mov    %r12d,%edx
    2c7b:	bf 01 00 00 00       	mov    $0x1,%edi
    2c80:	31 c0                	xor    %eax,%eax
    thread_data[x].running = 1;
    2c82:	41 c7 46 2c 01 00 00 00 	movl   $0x1,0x2c(%r14)
    2c8a:	48 8d 35 37 39 00 00 	lea    0x3937(%rip),%rsi        # 65c8 <_IO_stdin_used+0x5c8>
  for (int x = 0 ; x < thread_count ; x++) {
    2c91:	41 83 c4 01          	add    $0x1,%r12d
    2c95:	e8 96 f7 ff ff       	call   2430 <__printf_chk@plt>
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &timer_attr[x], &barriered_thread, &thread_data[x]);
    2c9a:	4c 89 f1             	mov    %r14,%rcx
    2c9d:	48 89 de             	mov    %rbx,%rsi
    2ca0:	48 89 ef             	mov    %rbp,%rdi
    2ca3:	4c 89 fa             	mov    %r15,%rdx
  for (int x = 0 ; x < thread_count ; x++) {
    2ca6:	49 81 c6 00 03 00 00 	add    $0x300,%r14
    2cad:	48 83 c5 08          	add    $0x8,%rbp
    2cb1:	48 83 c3 38          	add    $0x38,%rbx
    pthread_create(&thread[x], &timer_attr[x], &barriered_thread, &thread_data[x]);
    2cb5:	e8 96 f7 ff ff       	call   2450 <pthread_create@plt>
  for (int x = 0 ; x < thread_count ; x++) {
    2cba:	41 83 fc 06          	cmp    $0x6,%r12d
    2cbe:	75 b0                	jne    2c70 <main+0x6a0>
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    2cc0:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    2cc5:	48 8b 1d 3c 3d 00 00 	mov    0x3d3c(%rip),%rbx        # 6a08 <_IO_stdin_used+0xa08>

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2ccc:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    2cd1:	4d 89 ec             	mov    %r13,%r12
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2cd4:	bf 01 00 00 00       	mov    $0x1,%edi
    2cd9:	48 8d 2d 7f 36 00 00 	lea    0x367f(%rip),%rbp        # 635f <_IO_stdin_used+0x35f>
    thread_data[x].task_count = 0;
    2ce0:	49 89 98 28 15 00 00 	mov    %rbx,0x1528(%r8)
    thread_data[x].type = IO;
    2ce7:	41 c7 80 04 15 00 00 02 00 00 00 	movl   $0x2,0x1504(%r8)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2cf2:	e8 89 f6 ff ff       	call   2380 <calloc@plt>
    2cf7:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2cfc:	be 00 08 00 00       	mov    $0x800,%esi
    2d01:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    2d03:	49 89 80 40 15 00 00 	mov    %rax,0x1540(%r8)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    2d0a:	e8 81 f7 ff ff       	call   2490 <eventfd@plt>
    2d0f:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    2d14:	ba 07 00 00 00       	mov    $0x7,%edx
    2d19:	48 8d 35 ed 35 00 00 	lea    0x35ed(%rip),%rsi        # 630d <_IO_stdin_used+0x30d>
    2d20:	bf 01 00 00 00       	mov    $0x1,%edi
    2d25:	41 89 80 48 15 00 00 	mov    %eax,0x1548(%r8)
    2d2c:	31 c0                	xor    %eax,%eax
    thread_data[x].threads = thread_data;
    2d2e:	4d 89 80 10 15 00 00 	mov    %r8,0x1510(%r8)
    thread_data[x].thread_count = thread_count;
    2d35:	41 c7 80 18 15 00 00 06 00 00 00 	movl   $0x6,0x1518(%r8)
    thread_data[x].thread_index = x;
    2d40:	41 c7 80 00 15 00 00 07 00 00 00 	movl   $0x7,0x1500(%r8)
    2d4b:	e8 e0 f6 ff ff       	call   2430 <__printf_chk@plt>
    thread_data[x].type = IO;
    2d50:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2d55:	49 8d 7d 38          	lea    0x38(%r13),%rdi
    2d59:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    2d5e:	48 8d 15 4b 1d 00 00 	lea    0x1d4b(%rip),%rdx        # 4ab0 <io_thread>
    thread_data[x].type = IO;
    2d65:	49 8d 88 00 15 00 00 	lea    0x1500(%r8),%rcx
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    2d6c:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    2d73:	e8 d8 f6 ff ff       	call   2450 <pthread_create@plt>
    2d78:	ba 08 00 00 00       	mov    $0x8,%edx
    2d7d:	48 8d 35 a0 35 00 00 	lea    0x35a0(%rip),%rsi        # 6324 <_IO_stdin_used+0x324>
    2d84:	31 c0                	xor    %eax,%eax
    2d86:	bf 01 00 00 00       	mov    $0x1,%edi
    2d8b:	e8 a0 f6 ff ff       	call   2430 <__printf_chk@plt>
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    2d90:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    thread_data[x].buffers = &buffers[buffer_index];
    2d95:	48 8b 44 24 38       	mov    0x38(%rsp),%rax

    thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2d9a:	49 8d 7d 40          	lea    0x40(%r13),%rdi
    2d9e:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    2da3:	48 8d 15 96 09 00 00 	lea    0x996(%rip),%rdx        # 3740 <external_thread>
    2daa:	4c 8d 6c 24 50       	lea    0x50(%rsp),%r13
    thread_data[x].buffers = &buffers[buffer_index];
    2daf:	49 89 80 38 18 00 00 	mov    %rax,0x1838(%r8)
    thread_data[x].thread_count = thread_count;
    2db6:	48 8b 05 33 3c 00 00 	mov    0x3c33(%rip),%rax        # 69f0 <_IO_stdin_used+0x9f0>
    thread_data[x].type = EXTERNAL;
    2dbd:	49 8d 88 00 18 00 00 	lea    0x1800(%r8),%rcx
    thread_data[x].task_count = 0;
    2dc4:	49 89 98 28 18 00 00 	mov    %rbx,0x1828(%r8)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2dcb:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
    2dd2:	31 db                	xor    %ebx,%ebx
    thread_data[x].thread_count = thread_count;
    2dd4:	49 89 80 18 18 00 00 	mov    %rax,0x1818(%r8)
    thread_data[x].thread_index = x;
    2ddb:	48 8b 05 2e 3c 00 00 	mov    0x3c2e(%rip),%rax        # 6a10 <_IO_stdin_used+0xa10>
    thread_data[x].threads = thread_data;
    2de2:	4d 89 80 10 18 00 00 	mov    %r8,0x1810(%r8)
    thread_data[x].thread_index = x;
    2de9:	49 89 80 00 18 00 00 	mov    %rax,0x1800(%r8)
    thread_data[x].type = EXTERNAL;
    2df0:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    2df5:	e8 56 f6 ff ff       	call   2450 <pthread_create@plt>
    2dfa:	48 8d 3d 40 35 00 00 	lea    0x3540(%rip),%rdi        # 6341 <_IO_stdin_used+0x341>
    2e01:	e8 ca f4 ff ff       	call   22d0 <puts@plt>
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    2e06:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    2e0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    void * result; 
    pthread_join(thread[x], &result);
    2e10:	49 8b 3c dc          	mov    (%r12,%rbx,8),%rdi
    2e14:	4c 89 ee             	mov    %r13,%rsi
    2e17:	e8 b4 f6 ff ff       	call   24d0 <pthread_join@plt>
    2e1c:	89 da                	mov    %ebx,%edx
    2e1e:	48 89 ee             	mov    %rbp,%rsi
    2e21:	bf 01 00 00 00       	mov    $0x1,%edi
    2e26:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    2e28:	48 83 c3 01          	add    $0x1,%rbx
    2e2c:	e8 ff f5 ff ff       	call   2430 <__printf_chk@plt>
    2e31:	48 83 fb 09          	cmp    $0x9,%rbx
    2e35:	75 d9                	jne    2e10 <main+0x840>
    2e37:	49 8d 86 20 12 00 00 	lea    0x1220(%r14),%rax
  }
  long total = 0;
  long v = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
    2e3e:	31 ed                	xor    %ebp,%ebp
  long sends = 0;
    2e40:	31 c9                	xor    %ecx,%ecx
  long v = 0;
    2e42:	45 31 c9             	xor    %r9d,%r9d
  long total = 0;
    2e45:	45 31 e4             	xor    %r12d,%r12d
    2e48:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  long ingests = 0;
    2e4d:	45 31 db             	xor    %r11d,%r11d
    2e50:	4d 8d 6e 20          	lea    0x20(%r14),%r13
    2e54:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
  long received = 0;
    2e59:	31 db                	xor    %ebx,%ebx
    2e5b:	4d 89 de             	mov    %r11,%r14
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
      struct timespec start = thread_data[x].start[n];
      struct timespec end = thread_data[x].end[n];
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    2e5e:	49 bf db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r15
    2e68:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2e6d:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    2e72:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    2e77:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2e80:	49 63 45 08          	movslq 0x8(%r13),%rax
    2e84:	85 c0                	test   %eax,%eax
    2e86:	0f 8e c0 00 00 00    	jle    2f4c <main+0x97c>
    2e8c:	48 8d 34 80          	lea    (%rax,%rax,4),%rsi
    2e90:	49 8b 55 00          	mov    0x0(%r13),%rdx
    2e94:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    2e99:	48 8d 34 70          	lea    (%rax,%rsi,2),%rsi
    2e9d:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    2ea2:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    2ea7:	48 c1 e6 07          	shl    $0x7,%rsi
    2eab:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    2eb0:	48 01 d6             	add    %rdx,%rsi
    2eb3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2eb8:	48 8b 82 88 04 00 00 	mov    0x488(%rdx),%rax
      total += thread_data[x].tasks[n].n;
    2ebf:	48 03 8a 80 01 00 00 	add    0x180(%rdx),%rcx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2ec6:	48 81 c2 80 05 00 00 	add    $0x580,%rdx
      v += thread_data[x].tasks[n].v;
    2ecd:	4c 03 9a 80 fc ff ff 	add    -0x380(%rdx),%r11
      ingests += thread_data[x].tasks[n].ingest_count;
    2ed4:	4c 03 b2 00 ff ff ff 	add    -0x100(%rdx),%r14
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2edb:	48 03 a8 00 01 00 00 	add    0x100(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2ee2:	48 03 98 80 01 00 00 	add    0x180(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ee9:	48 03 a8 00 03 00 00 	add    0x300(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2ef0:	48 03 98 80 03 00 00 	add    0x380(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2ef7:	48 03 a8 00 05 00 00 	add    0x500(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2efe:	48 03 98 80 05 00 00 	add    0x580(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2f05:	48 03 a8 00 07 00 00 	add    0x700(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2f0c:	48 03 98 80 07 00 00 	add    0x780(%rax),%rbx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2f13:	48 03 a8 00 09 00 00 	add    0x900(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2f1a:	48 03 98 80 09 00 00 	add    0x980(%rax),%rbx
      sends += thread_data[x].tasks[n].sends;
    2f21:	4c 03 4a 80          	add    -0x80(%rdx),%r9
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    2f25:	48 03 a8 00 0b 00 00 	add    0xb00(%rax),%rbp
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    2f2c:	48 03 98 80 0b 00 00 	add    0xb80(%rax),%rbx
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    2f33:	48 39 f2             	cmp    %rsi,%rdx
    2f36:	75 80                	jne    2eb8 <main+0x8e8>
    2f38:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    2f3d:	4c 89 5c 24 10       	mov    %r11,0x10(%rsp)
    2f42:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    2f47:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2f4c:	45 31 e4             	xor    %r12d,%r12d
    2f4f:	49 83 bd e8 01 00 00 00 	cmpq   $0x0,0x1e8(%r13)
    2f57:	7e 7f                	jle    2fd8 <main+0xa08>
    2f59:	4c 89 ed             	mov    %r13,%rbp
    2f5c:	49 89 dd             	mov    %rbx,%r13
    2f5f:	4c 89 e3             	mov    %r12,%rbx
    2f62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      struct timespec start = thread_data[x].start[n];
    2f68:	48 8b 7d 60          	mov    0x60(%rbp),%rdi
    2f6c:	48 89 de             	mov    %rbx,%rsi
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2f6f:	48 83 c3 01          	add    $0x1,%rbx
    2f73:	48 c1 e6 04          	shl    $0x4,%rsi
      struct timespec start = thread_data[x].start[n];
    2f77:	48 01 f7             	add    %rsi,%rdi
      struct timespec end = thread_data[x].end[n];
    2f7a:	48 03 b5 e0 00 00 00 	add    0xe0(%rbp),%rsi
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    2f81:	48 8b 56 08          	mov    0x8(%rsi),%rdx
    2f85:	48 2b 57 08          	sub    0x8(%rdi),%rdx
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    2f89:	48 89 d0             	mov    %rdx,%rax
    2f8c:	49 f7 e7             	mul    %r15
    2f8f:	31 c0                	xor    %eax,%eax
    2f91:	48 89 d1             	mov    %rdx,%rcx
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    2f94:	48 8b 16             	mov    (%rsi),%rdx
    2f97:	48 8d 35 d5 33 00 00 	lea    0x33d5(%rip),%rsi        # 6373 <_IO_stdin_used+0x373>
    2f9e:	48 2b 17             	sub    (%rdi),%rdx
      printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
    2fa1:	48 c1 e9 12          	shr    $0x12,%rcx
    2fa5:	bf 01 00 00 00       	mov    $0x1,%edi
    2faa:	e8 81 f4 ff ff       	call   2430 <__printf_chk@plt>
    2faf:	48 8b 95 60 01 00 00 	mov    0x160(%rbp),%rdx
    2fb6:	48 8d 35 d4 33 00 00 	lea    0x33d4(%rip),%rsi        # 6391 <_IO_stdin_used+0x391>
    2fbd:	31 c0                	xor    %eax,%eax
    2fbf:	bf 01 00 00 00       	mov    $0x1,%edi
    2fc4:	e8 67 f4 ff ff       	call   2430 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    2fc9:	48 39 9d e8 01 00 00 	cmp    %rbx,0x1e8(%rbp)
    2fd0:	7f 96                	jg     2f68 <main+0x998>
    2fd2:	4c 89 eb             	mov    %r13,%rbx
    2fd5:	49 89 ed             	mov    %rbp,%r13
      printf("%ld iterations\n", thread_data[x].iteration_count);
    }
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    2fd8:	45 31 e4             	xor    %r12d,%r12d
    2fdb:	49 83 bd 68 02 00 00 00 	cmpq   $0x0,0x268(%r13)
    2fe3:	0f 8e a0 00 00 00    	jle    3089 <main+0xab9>
    2fe9:	4c 89 ed             	mov    %r13,%rbp
    2fec:	49 89 dd             	mov    %rbx,%r13
    2fef:	4c 89 e3             	mov    %r12,%rbx
    2ff2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    2ff8:	48 89 d9             	mov    %rbx,%rcx
    2ffb:	48 83 ec 08          	sub    $0x8,%rsp
    2fff:	48 8d 35 ea 35 00 00 	lea    0x35ea(%rip),%rsi        # 65f0 <_IO_stdin_used+0x5f0>
    3006:	bf 01 00 00 00       	mov    $0x1,%edi
    300b:	48 c1 e1 08          	shl    $0x8,%rcx
    300f:	48 03 8d f0 01 00 00 	add    0x1f0(%rbp),%rcx
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3016:	48 83 c3 01          	add    $0x1,%rbx
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    301a:	4c 8b a1 88 00 00 00 	mov    0x88(%rcx),%r12
    3021:	4c 2b 61 08          	sub    0x8(%rcx),%r12
      printf("all %d task %d synchronized in %lds %ldms %ld ns \n", thread_count, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3025:	4c 89 e0             	mov    %r12,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3028:	4c 8b 81 80 00 00 00 	mov    0x80(%rcx),%r8
    302f:	4c 2b 01             	sub    (%rcx),%r8
      printf("all %d task %d synchronized in %lds %ldms %ld ns \n", thread_count, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3032:	49 f7 e7             	mul    %r15
    3035:	8b 89 90 00 00 00    	mov    0x90(%rcx),%ecx
    303b:	41 54                	push   %r12
    303d:	31 c0                	xor    %eax,%eax
    303f:	48 c1 ea 12          	shr    $0x12,%rdx
    3043:	49 89 d1             	mov    %rdx,%r9
    3046:	ba 06 00 00 00       	mov    $0x6,%edx
    304b:	e8 e0 f3 ff ff       	call   2430 <__printf_chk@plt>
    3050:	48 8d 35 56 33 00 00 	lea    0x3356(%rip),%rsi        # 63ad <_IO_stdin_used+0x3ad>
    3057:	bf 01 00 00 00       	mov    $0x1,%edi
      printf("%ldns per thread\n", (seconds2 / thread_count));
    305c:	48 b8 ab aa aa aa aa aa aa aa 	movabs $0xaaaaaaaaaaaaaaab,%rax
    3066:	49 f7 e4             	mul    %r12
    3069:	31 c0                	xor    %eax,%eax
    306b:	48 c1 ea 02          	shr    $0x2,%rdx
    306f:	e8 bc f3 ff ff       	call   2430 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3074:	58                   	pop    %rax
    3075:	5a                   	pop    %rdx
    3076:	48 39 9d 68 02 00 00 	cmp    %rbx,0x268(%rbp)
    307d:	0f 8f 75 ff ff ff    	jg     2ff8 <main+0xa28>
    3083:	4c 89 eb             	mov    %r13,%rbx
    3086:	49 89 ed             	mov    %rbp,%r13
    3089:	49 8b 95 70 02 00 00 	mov    0x270(%r13),%rdx
    3090:	48 8d 35 0a 33 00 00 	lea    0x330a(%rip),%rsi        # 63a1 <_IO_stdin_used+0x3a1>
    3097:	bf 01 00 00 00       	mov    $0x1,%edi
    309c:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < thread_count ; x++) {
    309e:	49 81 c5 00 03 00 00 	add    $0x300,%r13
    30a5:	e8 86 f3 ff ff       	call   2430 <__printf_chk@plt>
    30aa:	4c 39 6c 24 28       	cmp    %r13,0x28(%rsp)
    30af:	0f 85 cb fd ff ff    	jne    2e80 <main+0x8b0>
    30b5:	4c 8b 64 24 08       	mov    0x8(%rsp),%r12
    30ba:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    30bf:	48 8d 35 f9 32 00 00 	lea    0x32f9(%rip),%rsi        # 63bf <_IO_stdin_used+0x3bf>
    30c6:	31 c0                	xor    %eax,%eax
    30c8:	bf 01 00 00 00       	mov    $0x1,%edi
    30cd:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    30d2:	4c 89 74 24 10       	mov    %r14,0x10(%rsp)
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total Protected %ld\n", protected_state->protected);
  printf("Total V %ld\n", v);
  printf("\n");
  printf("Total Protected per second %ld\n", protected_state->protected / DURATION);
    30d7:	49 bd 89 88 88 88 88 88 88 88 	movabs $0x8888888888888889,%r13
    30e1:	4c 89 e2             	mov    %r12,%rdx
    30e4:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    30e9:	e8 42 f3 ff ff       	call   2430 <__printf_chk@plt>
    30ee:	bf 0a 00 00 00       	mov    $0xa,%edi
    30f3:	e8 c8 f1 ff ff       	call   22c0 <putchar@plt>
    30f8:	4c 8b 74 24 40       	mov    0x40(%rsp),%r14
    30fd:	48 8d 35 cf 32 00 00 	lea    0x32cf(%rip),%rsi        # 63d3 <_IO_stdin_used+0x3d3>
    3104:	31 c0                	xor    %eax,%eax
    3106:	bf 01 00 00 00       	mov    $0x1,%edi
    310b:	49 8b 16             	mov    (%r14),%rdx
    310e:	e8 1d f3 ff ff       	call   2430 <__printf_chk@plt>
    3113:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    3118:	48 8d 35 c9 32 00 00 	lea    0x32c9(%rip),%rsi        # 63e8 <_IO_stdin_used+0x3e8>
    311f:	31 c0                	xor    %eax,%eax
    3121:	bf 01 00 00 00       	mov    $0x1,%edi
    3126:	e8 05 f3 ff ff       	call   2430 <__printf_chk@plt>
    312b:	bf 0a 00 00 00       	mov    $0xa,%edi
    3130:	e8 8b f1 ff ff       	call   22c0 <putchar@plt>
    3135:	49 8b 36             	mov    (%r14),%rsi
    3138:	bf 01 00 00 00       	mov    $0x1,%edi
    313d:	48 89 f0             	mov    %rsi,%rax
    3140:	49 f7 ed             	imul   %r13
    3143:	31 c0                	xor    %eax,%eax
    3145:	48 01 f2             	add    %rsi,%rdx
    3148:	48 c1 fe 3f          	sar    $0x3f,%rsi
    314c:	48 c1 fa 04          	sar    $0x4,%rdx
    3150:	48 29 f2             	sub    %rsi,%rdx
    3153:	48 8d 35 ce 34 00 00 	lea    0x34ce(%rip),%rsi        # 6628 <_IO_stdin_used+0x628>
    315a:	e8 d1 f2 ff ff       	call   2430 <__printf_chk@plt>
    315f:	49 8b 96 80 00 00 00 	mov    0x80(%r14),%rdx
    3166:	48 8d 35 db 34 00 00 	lea    0x34db(%rip),%rsi        # 6648 <_IO_stdin_used+0x648>
    316d:	31 c0                	xor    %eax,%eax
    316f:	bf 01 00 00 00       	mov    $0x1,%edi
    3174:	e8 b7 f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3179:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    317e:	bf 01 00 00 00       	mov    $0x1,%edi
    3183:	48 8d 35 e6 34 00 00 	lea    0x34e6(%rip),%rsi        # 6670 <_IO_stdin_used+0x670>
    318a:	4c 89 d8             	mov    %r11,%rax
    318d:	49 f7 ed             	imul   %r13
    3190:	31 c0                	xor    %eax,%eax
    3192:	4c 01 da             	add    %r11,%rdx
    3195:	49 c1 fb 3f          	sar    $0x3f,%r11
    3199:	48 c1 fa 04          	sar    $0x4,%rdx
    319d:	4c 29 da             	sub    %r11,%rdx
    31a0:	e8 8b f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    31a5:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    31aa:	bf 01 00 00 00       	mov    $0x1,%edi
    31af:	48 8d 35 ea 34 00 00 	lea    0x34ea(%rip),%rsi        # 66a0 <_IO_stdin_used+0x6a0>
    31b6:	48 89 c8             	mov    %rcx,%rax
    31b9:	49 f7 ed             	imul   %r13
    31bc:	31 c0                	xor    %eax,%eax
    31be:	48 01 ca             	add    %rcx,%rdx
    31c1:	48 c1 f9 3f          	sar    $0x3f,%rcx
    31c5:	48 c1 fa 04          	sar    $0x4,%rdx
    31c9:	48 29 ca             	sub    %rcx,%rdx
    31cc:	e8 5f f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    31d1:	4c 89 e0             	mov    %r12,%rax
    31d4:	bf 01 00 00 00       	mov    $0x1,%edi
    31d9:	48 8d 35 f0 34 00 00 	lea    0x34f0(%rip),%rsi        # 66d0 <_IO_stdin_used+0x6d0>
    31e0:	49 f7 ed             	imul   %r13
    31e3:	4c 01 e2             	add    %r12,%rdx
    31e6:	49 c1 fc 3f          	sar    $0x3f,%r12
    31ea:	31 c0                	xor    %eax,%eax
    31ec:	48 c1 fa 04          	sar    $0x4,%rdx
    31f0:	4c 29 e2             	sub    %r12,%rdx
    31f3:	e8 38 f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    31f8:	48 89 e8             	mov    %rbp,%rax
    31fb:	bf 01 00 00 00       	mov    $0x1,%edi
    3200:	48 8d 35 ee 31 00 00 	lea    0x31ee(%rip),%rsi        # 63f5 <_IO_stdin_used+0x3f5>
    3207:	49 f7 ed             	imul   %r13
    320a:	31 c0                	xor    %eax,%eax
    320c:	48 01 ea             	add    %rbp,%rdx
    320f:	48 c1 fd 3f          	sar    $0x3f,%rbp
    3213:	48 c1 fa 04          	sar    $0x4,%rdx
    3217:	48 29 ea             	sub    %rbp,%rdx
    321a:	e8 11 f2 ff ff       	call   2430 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    321f:	48 89 d8             	mov    %rbx,%rax
    3222:	bf 01 00 00 00       	mov    $0x1,%edi
    3227:	48 8d 35 d8 31 00 00 	lea    0x31d8(%rip),%rsi        # 6406 <_IO_stdin_used+0x406>
    322e:	49 f7 ed             	imul   %r13
    3231:	31 c0                	xor    %eax,%eax
    3233:	48 01 da             	add    %rbx,%rdx
    3236:	48 c1 fb 3f          	sar    $0x3f,%rbx
    323a:	48 c1 fa 04          	sar    $0x4,%rdx
    323e:	48 29 da             	sub    %rbx,%rdx
    3241:	e8 ea f1 ff ff       	call   2430 <__printf_chk@plt>
  // verify(thread_data, thread_count);
  return 0;

}
    3246:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    324b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3254:	75 4e                	jne    32a4 <main+0xcd4>
    3256:	48 83 c4 68          	add    $0x68,%rsp
    325a:	31 c0                	xor    %eax,%eax
    325c:	5b                   	pop    %rbx
    325d:	5d                   	pop    %rbp
    325e:	41 5c                	pop    %r12
    3260:	41 5d                	pop    %r13
    3262:	41 5e                	pop    %r14
    3264:	41 5f                	pop    %r15
    3266:	c3                   	ret
    3267:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          thread_data[x].tasks[y].run = barriered_work; 
    3270:	48 8d 05 29 20 00 00 	lea    0x2029(%rip),%rax        # 52a0 <barriered_work>
    3277:	41 bd 06 00 00 00    	mov    $0x6,%r13d
    327d:	48 89 85 08 02 00 00 	mov    %rax,0x208(%rbp)
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3284:	e9 e1 f7 ff ff       	jmp    2a6a <main+0x49a>
    3289:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            thread_data[x].tasks[y].protected = do_protected_write; 
    3290:	48 8d 05 09 01 00 00 	lea    0x109(%rip),%rax        # 33a0 <do_protected_write>
    3297:	4b 89 84 27 10 02 00 00 	mov    %rax,0x210(%r15,%r12,1)
    329f:	e9 ab f5 ff ff       	jmp    284f <main+0x27f>
}
    32a4:	e8 67 f0 ff ff       	call   2310 <__stack_chk_fail@plt>
    32a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000032b0 <_start>:
    32b0:	f3 0f 1e fa          	endbr64
    32b4:	31 ed                	xor    %ebp,%ebp
    32b6:	49 89 d1             	mov    %rdx,%r9
    32b9:	5e                   	pop    %rsi
    32ba:	48 89 e2             	mov    %rsp,%rdx
    32bd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    32c1:	50                   	push   %rax
    32c2:	54                   	push   %rsp
    32c3:	45 31 c0             	xor    %r8d,%r8d
    32c6:	31 c9                	xor    %ecx,%ecx
    32c8:	48 8d 3d 01 f3 ff ff 	lea    -0xcff(%rip),%rdi        # 25d0 <main>
    32cf:	ff 15 03 5d 00 00    	call   *0x5d03(%rip)        # 8fd8 <__libc_start_main@GLIBC_2.34>
    32d5:	f4                   	hlt
    32d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000032e0 <deregister_tm_clones>:
    32e0:	48 8d 3d 39 5d 00 00 	lea    0x5d39(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    32e7:	48 8d 05 32 5d 00 00 	lea    0x5d32(%rip),%rax        # 9020 <stderr@GLIBC_2.2.5>
    32ee:	48 39 f8             	cmp    %rdi,%rax
    32f1:	74 15                	je     3308 <deregister_tm_clones+0x28>
    32f3:	48 8b 05 e6 5c 00 00 	mov    0x5ce6(%rip),%rax        # 8fe0 <_ITM_deregisterTMCloneTable@Base>
    32fa:	48 85 c0             	test   %rax,%rax
    32fd:	74 09                	je     3308 <deregister_tm_clones+0x28>
    32ff:	ff e0                	jmp    *%rax
    3301:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3308:	c3                   	ret
    3309:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003310 <register_tm_clones>:
    3310:	48 8d 3d 09 5d 00 00 	lea    0x5d09(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    3317:	48 8d 35 02 5d 00 00 	lea    0x5d02(%rip),%rsi        # 9020 <stderr@GLIBC_2.2.5>
    331e:	48 29 fe             	sub    %rdi,%rsi
    3321:	48 89 f0             	mov    %rsi,%rax
    3324:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3328:	48 c1 f8 03          	sar    $0x3,%rax
    332c:	48 01 c6             	add    %rax,%rsi
    332f:	48 d1 fe             	sar    %rsi
    3332:	74 14                	je     3348 <register_tm_clones+0x38>
    3334:	48 8b 05 b5 5c 00 00 	mov    0x5cb5(%rip),%rax        # 8ff0 <_ITM_registerTMCloneTable@Base>
    333b:	48 85 c0             	test   %rax,%rax
    333e:	74 08                	je     3348 <register_tm_clones+0x38>
    3340:	ff e0                	jmp    *%rax
    3342:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3348:	c3                   	ret
    3349:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003350 <__do_global_dtors_aux>:
    3350:	f3 0f 1e fa          	endbr64
    3354:	80 3d cd 5c 00 00 00 	cmpb   $0x0,0x5ccd(%rip)        # 9028 <completed.0>
    335b:	75 2b                	jne    3388 <__do_global_dtors_aux+0x38>
    335d:	55                   	push   %rbp
    335e:	48 83 3d 92 5c 00 00 00 	cmpq   $0x0,0x5c92(%rip)        # 8ff8 <__cxa_finalize@GLIBC_2.2.5>
    3366:	48 89 e5             	mov    %rsp,%rbp
    3369:	74 0c                	je     3377 <__do_global_dtors_aux+0x27>
    336b:	48 8b 3d 96 5c 00 00 	mov    0x5c96(%rip),%rdi        # 9008 <__dso_handle>
    3372:	e8 29 ef ff ff       	call   22a0 <__cxa_finalize@plt>
    3377:	e8 64 ff ff ff       	call   32e0 <deregister_tm_clones>
    337c:	c6 05 a5 5c 00 00 01 	movb   $0x1,0x5ca5(%rip)        # 9028 <completed.0>
    3383:	5d                   	pop    %rbp
    3384:	c3                   	ret
    3385:	0f 1f 00             	nopl   (%rax)
    3388:	c3                   	ret
    3389:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003390 <frame_dummy>:
    3390:	f3 0f 1e fa          	endbr64
    3394:	e9 77 ff ff ff       	jmp    3310 <register_tm_clones>
    3399:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000033a0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    33a0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    33a4:	48 8b 87 18 02 00 00 	mov    0x218(%rdi),%rax
    33ab:	48 8b 40 30          	mov    0x30(%rax),%rax
  data->v++; // thread local
    33af:	48 83 87 00 02 00 00 01 	addq   $0x1,0x200(%rdi)
  if (protected->balance > 0) {
    33b7:	48 8b 88 80 00 00 00 	mov    0x80(%rax),%rcx
  protected->protected++; // shared between all threads
    33be:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    33c2:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    33c9:	48 85 c9             	test   %rcx,%rcx
    33cc:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    33d3:	48 0f 4f d6          	cmovg  %rsi,%rdx
    33d7:	48 89 90 80 00 00 00 	mov    %rdx,0x80(%rax)
}
    33de:	31 c0                	xor    %eax,%eax
    33e0:	c3                   	ret
    33e1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    33ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000033f0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    33f0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    33f4:	48 63 87 84 02 00 00 	movslq 0x284(%rdi),%rax
    33fb:	85 c0                	test   %eax,%eax
    33fd:	7e 57                	jle    3456 <barriered_reset+0x66>
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    33ff:	48 63 97 20 02 00 00 	movslq 0x220(%rdi),%rdx
    3406:	48 8b 8f 18 02 00 00 	mov    0x218(%rdi),%rcx
    340d:	48 8d 14 52          	lea    (%rdx,%rdx,2),%rdx
      data->thread->tasks[x].available = 1; 
    3411:	48 8b 71 20          	mov    0x20(%rcx),%rsi
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    3415:	48 c1 e2 08          	shl    $0x8,%rdx
    3419:	48 03 51 10          	add    0x10(%rcx),%rdx
    341d:	48 8d 0c 80          	lea    (%rax,%rax,4),%rcx
    3421:	48 8d 0c 48          	lea    (%rax,%rcx,2),%rcx
    3425:	48 8b 52 20          	mov    0x20(%rdx),%rdx
      data->thread->tasks[x].available = 1; 
    3429:	31 c0                	xor    %eax,%eax
    342b:	48 c1 e1 07          	shl    $0x7,%rcx
    342f:	90                   	nop
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
    3430:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index].tasks[x].prearrive++; 
    3438:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    3440:	c7 84 06 80 02 00 00 01 00 00 00 	movl   $0x1,0x280(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    344b:	48 05 80 05 00 00    	add    $0x580,%rax
    3451:	48 39 c1             	cmp    %rax,%rcx
    3454:	75 da                	jne    3430 <barriered_reset+0x40>
  asm volatile ("mfence" ::: "memory");
    3456:	0f ae f0             	mfence
}
    3459:	31 c0                	xor    %eax,%eax
    345b:	c3                   	ret
    345c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003460 <barriered_thread>:
void* barriered_thread(void *arg) {
    3460:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    3464:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
    3468:	0f 85 c5 02 00 00    	jne    3733 <barriered_thread+0x2d3>
void* barriered_thread(void *arg) {
    346e:	41 56                	push   %r14
    3470:	41 55                	push   %r13
    3472:	45 31 ed             	xor    %r13d,%r13d
    3475:	41 54                	push   %r12
    3477:	49 89 fc             	mov    %rdi,%r12
    347a:	55                   	push   %rbp
    347b:	53                   	push   %rbx
    347c:	31 db                	xor    %ebx,%ebx
    347e:	66 90                	xchg   %ax,%ax
    if (t >= data->task_count) {
    3480:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    3485:	39 da                	cmp    %ebx,%edx
    3487:	7f 13                	jg     349c <barriered_thread+0x3c>
      data->cycles++;
    3489:	49 83 84 24 90 02 00 00 01 	addq   $0x1,0x290(%r12)
    for (; t < data->task_count; t++) {
    3492:	31 db                	xor    %ebx,%ebx
    3494:	85 d2                	test   %edx,%edx
    3496:	0f 8e 7c 01 00 00    	jle    3618 <barriered_thread+0x1b8>
    349c:	48 63 c3             	movslq %ebx,%rax
    349f:	48 8d 0c 80          	lea    (%rax,%rax,4),%rcx
    34a3:	48 8d 2c 48          	lea    (%rax,%rcx,2),%rbp
    34a7:	48 c1 e5 07          	shl    $0x7,%rbp
    34ab:	eb 15                	jmp    34c2 <barriered_thread+0x62>
    34ad:	0f 1f 00             	nopl   (%rax)
    34b0:	83 c3 01             	add    $0x1,%ebx
    34b3:	48 81 c5 80 05 00 00 	add    $0x580,%rbp
    34ba:	39 d3                	cmp    %edx,%ebx
    34bc:	0f 8d 56 01 00 00    	jge    3618 <barriered_thread+0x1b8>
      if (data->tasks[t].available == 1) {
    34c2:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    34c7:	48 8d 0c 28          	lea    (%rax,%rbp,1),%rcx
    34cb:	83 b9 80 02 00 00 01 	cmpl   $0x1,0x280(%rcx)
    34d2:	75 dc                	jne    34b0 <barriered_thread+0x50>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    34d4:	41 8b 7c 24 18       	mov    0x18(%r12),%edi
          previous = t - 1;
    34d9:	83 ea 01             	sub    $0x1,%edx
    34dc:	8d 73 ff             	lea    -0x1(%rbx),%esi
    34df:	85 db                	test   %ebx,%ebx
    34e1:	0f 4f d6             	cmovg  %esi,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    34e4:	85 ff                	test   %edi,%edi
    34e6:	0f 8e cc 01 00 00    	jle    36b8 <barriered_thread+0x258>
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    34ec:	48 63 d2             	movslq %edx,%rdx
    34ef:	44 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9d
        int prearrive = 0; 
    34f6:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    34f9:	45 31 f6             	xor    %r14d,%r14d
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    34fc:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
          if (data->threads[thread].tasks[previous].prearrive == data->tasks[t].prearrive) {
    3500:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
    3507:	48 8d 34 42          	lea    (%rdx,%rax,2),%rsi
    350b:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    3510:	48 63 d7             	movslq %edi,%rdx
    3513:	48 8d 0c 52          	lea    (%rdx,%rdx,2),%rcx
    3517:	48 c1 e6 07          	shl    $0x7,%rsi
    351b:	48 83 c0 20          	add    $0x20,%rax
    351f:	48 c1 e1 08          	shl    $0x8,%rcx
    3523:	48 01 c1             	add    %rax,%rcx
    3526:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3530:	48 8b 10             	mov    (%rax),%rdx
    3533:	48 01 f2             	add    %rsi,%rdx
    3536:	44 3b 8a 80 00 00 00 	cmp    0x80(%rdx),%r9d
    353d:	75 04                	jne    3543 <barriered_thread+0xe3>
            arrived++;
    353f:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread].tasks[previous].prearrive == data->tasks[t].prearrive) {
    3543:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    354a:	75 04                	jne    3550 <barriered_thread+0xf0>
            prearrive++;
    354c:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    3550:	48 05 00 03 00 00    	add    $0x300,%rax
    3556:	48 39 c8             	cmp    %rcx,%rax
    3559:	75 d5                	jne    3530 <barriered_thread+0xd0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    355b:	44 39 d7             	cmp    %r10d,%edi
    355e:	0f 84 cc 00 00 00    	je     3630 <barriered_thread+0x1d0>
    3564:	45 85 d2             	test   %r10d,%r10d
    3567:	0f 84 c3 00 00 00    	je     3630 <barriered_thread+0x1d0>
        if (arrived == 0 || arrived == data->thread_count) {
    356d:	45 85 f6             	test   %r14d,%r14d
    3570:	74 0b                	je     357d <barriered_thread+0x11d>
    3572:	45 39 74 24 18       	cmp    %r14d,0x18(%r12)
    3577:	0f 85 9b 00 00 00    	jne    3618 <barriered_thread+0x1b8>
    357d:	49 8b 44 24 20       	mov    0x20(%r12),%rax
          data->tasks[t].prearrive++;
    3582:	48 01 e8             	add    %rbp,%rax
    3585:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    358c:	85 db                	test   %ebx,%ebx
    358e:	75 16                	jne    35a6 <barriered_thread+0x146>
    3590:	49 8b b4 24 00 02 00 00 	mov    0x200(%r12),%rsi
    3598:	49 3b b4 24 08 02 00 00 	cmp    0x208(%r12),%rsi
    35a0:	0f 8c 6a 01 00 00    	jl     3710 <barriered_thread+0x2b0>
          data->tasks[t].available = 0;
    35a6:	c7 80 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%rax)
          data->tasks[t].run(&data->threads[data->thread_index].tasks[t]);
    35b0:	49 63 14 24          	movslq (%r12),%rdx
    35b4:	48 8d 14 52          	lea    (%rdx,%rdx,2),%rdx
    35b8:	48 c1 e2 08          	shl    $0x8,%rdx
    35bc:	49 03 54 24 10       	add    0x10(%r12),%rdx
    35c1:	48 8b 7a 20          	mov    0x20(%rdx),%rdi
    35c5:	48 01 ef             	add    %rbp,%rdi
    35c8:	ff 90 08 02 00 00    	call   *0x208(%rax)
          data->tasks[t].arrived++;
    35ce:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    35d3:	48 01 e8             	add    %rbp,%rax
    35d6:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    35dd:	41 8b 44 24 28       	mov    0x28(%r12),%eax
          data->iteration_count++;
    35e2:	49 83 84 24 80 01 00 00 01 	addq   $0x1,0x180(%r12)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    35eb:	83 e8 01             	sub    $0x1,%eax
    35ee:	39 d8                	cmp    %ebx,%eax
    35f0:	74 56                	je     3648 <barriered_thread+0x1e8>
          asm volatile ("mfence" ::: "memory");
    35f2:	0f ae f0             	mfence
          if (waiting == 0) {
    35f5:	45 85 ed             	test   %r13d,%r13d
    35f8:	0f 84 82 00 00 00    	je     3680 <barriered_thread+0x220>
    for (; t < data->task_count; t++) {
    35fe:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    3603:	83 c3 01             	add    $0x1,%ebx
    3606:	48 81 c5 80 05 00 00 	add    $0x580,%rbp
    360d:	39 d3                	cmp    %edx,%ebx
    360f:	0f 8c ad fe ff ff    	jl     34c2 <barriered_thread+0x62>
    3615:	0f 1f 00             	nopl   (%rax)
  while (data->running == 1) {
    3618:	41 83 7c 24 2c 01    	cmpl   $0x1,0x2c(%r12)
    361e:	0f 84 5c fe ff ff    	je     3480 <barriered_thread+0x20>
}
    3624:	5b                   	pop    %rbx
    3625:	31 c0                	xor    %eax,%eax
    3627:	5d                   	pop    %rbp
    3628:	41 5c                	pop    %r12
    362a:	41 5d                	pop    %r13
    362c:	41 5e                	pop    %r14
    362e:	c3                   	ret
    362f:	90                   	nop
          if (waiting == 1) {
    3630:	41 83 fd 01          	cmp    $0x1,%r13d
    3634:	0f 84 8e 00 00 00    	je     36c8 <barriered_thread+0x268>
        int arrived = 0; 
    363a:	45 31 ed             	xor    %r13d,%r13d
    363d:	e9 2b ff ff ff       	jmp    356d <barriered_thread+0x10d>
    3642:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    3648:	49 8b b4 24 00 02 00 00 	mov    0x200(%r12),%rsi
    3650:	49 3b b4 24 08 02 00 00 	cmp    0x208(%r12),%rsi
    3658:	7d 98                	jge    35f2 <barriered_thread+0x192>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    365a:	48 c1 e6 04          	shl    $0x4,%rsi
    365e:	bf 04 00 00 00       	mov    $0x4,%edi
    3663:	49 03 b4 24 00 01 00 00 	add    0x100(%r12),%rsi
    366b:	e8 80 ec ff ff       	call   22f0 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    3670:	49 83 84 24 00 02 00 00 01 	addq   $0x1,0x200(%r12)
    3679:	e9 74 ff ff ff       	jmp    35f2 <barriered_thread+0x192>
    367e:	66 90                	xchg   %ax,%ax
            data->task_snapshot[data->task_timestamp_count].task = t;
    3680:	49 8b b4 24 80 02 00 00 	mov    0x280(%r12),%rsi
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    3688:	bf 04 00 00 00       	mov    $0x4,%edi
            waiting = 1;
    368d:	41 bd 01 00 00 00    	mov    $0x1,%r13d
            data->task_snapshot[data->task_timestamp_count].task = t;
    3693:	48 c1 e6 08          	shl    $0x8,%rsi
    3697:	49 03 b4 24 10 02 00 00 	add    0x210(%r12),%rsi
    369f:	89 9e 90 00 00 00    	mov    %ebx,0x90(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    36a5:	e8 46 ec ff ff       	call   22f0 <clock_gettime@plt>
    for (; t < data->task_count; t++) {
    36aa:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    36af:	e9 fc fd ff ff       	jmp    34b0 <barriered_thread+0x50>
    36b4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    36b8:	41 83 fd 01          	cmp    $0x1,%r13d
    36bc:	0f 85 c0 fe ff ff    	jne    3582 <barriered_thread+0x122>
        int arrived = 0; 
    36c2:	45 31 f6             	xor    %r14d,%r14d
    36c5:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    36c8:	49 8b b4 24 80 02 00 00 	mov    0x280(%r12),%rsi
    36d0:	bf 04 00 00 00       	mov    $0x4,%edi
    36d5:	48 c1 e6 08          	shl    $0x8,%rsi
    36d9:	49 03 b4 24 10 02 00 00 	add    0x210(%r12),%rsi
    36e1:	48 83 ee 80          	sub    $0xffffffffffffff80,%rsi
    36e5:	e8 06 ec ff ff       	call   22f0 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    36ea:	49 8b 84 24 80 02 00 00 	mov    0x280(%r12),%rax
    36f2:	48 83 c0 01          	add    $0x1,%rax
    36f6:	48 99                	cqto
    36f8:	49 f7 bc 24 88 02 00 00 	idivq  0x288(%r12)
    3700:	49 89 94 24 80 02 00 00 	mov    %rdx,0x280(%r12)
          if (waiting == 3) {
    3708:	e9 2d ff ff ff       	jmp    363a <barriered_thread+0x1da>
    370d:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    3710:	48 c1 e6 04          	shl    $0x4,%rsi
    3714:	bf 04 00 00 00       	mov    $0x4,%edi
    3719:	49 03 b4 24 80 00 00 00 	add    0x80(%r12),%rsi
    3721:	e8 ca eb ff ff       	call   22f0 <clock_gettime@plt>
          data->tasks[t].available = 0;
    3726:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    372b:	48 01 e8             	add    %rbp,%rax
    372e:	e9 73 fe ff ff       	jmp    35a6 <barriered_thread+0x146>
}
    3733:	31 c0                	xor    %eax,%eax
    3735:	c3                   	ret
    3736:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003740 <external_thread>:
void * external_thread(void *arg) {
    3740:	f3 0f 1e fa          	endbr64
    3744:	41 55                	push   %r13
    3746:	41 54                	push   %r12
    3748:	55                   	push   %rbp
    3749:	53                   	push   %rbx
    374a:	48 83 ec 38          	sub    $0x38,%rsp
  struct timespec req = {
    374e:	66 0f 6f 05 9a 31 00 00 	movdqa 0x319a(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
void * external_thread(void *arg) {
    3756:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    375f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3764:	31 c0                	xor    %eax,%eax
  while (data->running == 1) {
    3766:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
  struct timespec req = {
    376a:	0f 29 04 24          	movaps %xmm0,(%rsp)
  while (data->running == 1) {
    376e:	75 6c                	jne    37dc <external_thread+0x9c>
    3770:	49 89 fd             	mov    %rdi,%r13
    3773:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    3778:	48 89 e3             	mov    %rsp,%rbx
        data->buffers->buffer[x].data = "Hello world";
    377b:	4c 8d 25 82 28 00 00 	lea    0x2882(%rip),%r12        # 6004 <_IO_stdin_used+0x4>
    3782:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    nanosleep(&req , &rem);
    3788:	48 89 ee             	mov    %rbp,%rsi
    378b:	48 89 df             	mov    %rbx,%rdi
    378e:	e8 9d eb ff ff       	call   2330 <nanosleep@plt>
    for (int x = 0; x < data->buffers->count; x++) {
    3793:	49 8b 45 38          	mov    0x38(%r13),%rax
    3797:	48 63 10             	movslq (%rax),%rdx
    379a:	85 d2                	test   %edx,%edx
    379c:	7e 34                	jle    37d2 <external_thread+0x92>
    379e:	48 8b 40 08          	mov    0x8(%rax),%rax
    37a2:	48 c1 e2 08          	shl    $0x8,%rdx
    37a6:	48 01 c2             	add    %rax,%rdx
    37a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      if (data->buffers->buffer[x].available == 0) {
    37b0:	8b 88 80 00 00 00    	mov    0x80(%rax),%ecx
    37b6:	85 c9                	test   %ecx,%ecx
    37b8:	75 0d                	jne    37c7 <external_thread+0x87>
        data->buffers->buffer[x].data = "Hello world";
    37ba:	4c 89 20             	mov    %r12,(%rax)
        data->buffers->buffer[x].available = 1;
    37bd:	c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax)
    for (int x = 0; x < data->buffers->count; x++) {
    37c7:	48 05 00 01 00 00    	add    $0x100,%rax
    37cd:	48 39 c2             	cmp    %rax,%rdx
    37d0:	75 de                	jne    37b0 <external_thread+0x70>
    asm volatile ("mfence" ::: "memory");
    37d2:	0f ae f0             	mfence
  while (data->running == 1) {
    37d5:	41 83 7d 2c 01       	cmpl   $0x1,0x2c(%r13)
    37da:	74 ac                	je     3788 <external_thread+0x48>
}
    37dc:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    37e1:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    37ea:	75 0d                	jne    37f9 <external_thread+0xb9>
    37ec:	48 83 c4 38          	add    $0x38,%rsp
    37f0:	31 c0                	xor    %eax,%eax
    37f2:	5b                   	pop    %rbx
    37f3:	5d                   	pop    %rbp
    37f4:	41 5c                	pop    %r12
    37f6:	41 5d                	pop    %r13
    37f8:	c3                   	ret
    37f9:	e8 12 eb ff ff       	call   2310 <__stack_chk_fail@plt>
    37fe:	66 90                	xchg   %ax,%ax

0000000000003800 <timer_thread>:
void* timer_thread(void *arg) {
    3800:	f3 0f 1e fa          	endbr64
    3804:	41 57                	push   %r15
    3806:	48 8d 35 03 28 00 00 	lea    0x2803(%rip),%rsi        # 6010 <_IO_stdin_used+0x10>
    380d:	49 89 ff             	mov    %rdi,%r15
    3810:	41 56                	push   %r14
    3812:	41 55                	push   %r13
    3814:	41 54                	push   %r12
    3816:	55                   	push   %rbp
    3817:	53                   	push   %rbx
    3818:	48 83 ec 58          	sub    $0x58,%rsp
    381c:	8b 17                	mov    (%rdi),%edx
    381e:	bf 01 00 00 00       	mov    $0x1,%edi
    3823:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    382c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3831:	31 c0                	xor    %eax,%eax
    3833:	e8 f8 eb ff ff       	call   2430 <__printf_chk@plt>
  struct timespec preempt = {
    3838:	66 0f 6f 05 b0 30 00 00 	movdqa 0x30b0(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
    3840:	ba 30 75 00 00       	mov    $0x7530,%edx
    3845:	31 c0                	xor    %eax,%eax
    3847:	48 8d 35 d4 27 00 00 	lea    0x27d4(%rip),%rsi        # 6022 <_IO_stdin_used+0x22>
    384e:	bf 01 00 00 00       	mov    $0x1,%edi
    3853:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3858:	e8 d3 eb ff ff       	call   2430 <__printf_chk@plt>
  while (data->running && n < times) {
    385d:	45 8b 6f 2c          	mov    0x2c(%r15),%r13d
    3861:	45 85 ed             	test   %r13d,%r13d
    3864:	0f 84 b6 00 00 00    	je     3920 <timer_thread+0x120>
  int n = 0;
    386a:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    386d:	45 31 ed             	xor    %r13d,%r13d
    3870:	49 89 e4             	mov    %rsp,%r12
    y++;
    3873:	31 db                	xor    %ebx,%ebx
    3875:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    nanosleep(&preempt , &rem2);
    387a:	48 89 ef             	mov    %rbp,%rdi
    387d:	4c 89 e6             	mov    %r12,%rsi
    n++;
    3880:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    3884:	e8 a7 ea ff ff       	call   2330 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3889:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    388d:	41 8d 7d 01          	lea    0x1(%r13),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    3891:	85 c0                	test   %eax,%eax
    3893:	7e 66                	jle    38fb <timer_thread+0xfb>
    3895:	49 8b 77 10          	mov    0x10(%r15),%rsi
        data->threads[x].tasks[y].scheduled = 0;
    3899:	4b 8d 54 ad 00       	lea    0x0(%r13,%r13,4),%rdx
    389e:	4c 8d 04 40          	lea    (%rax,%rax,2),%r8
    38a2:	4d 8d 4c 55 00       	lea    0x0(%r13,%rdx,2),%r9
    38a7:	49 c1 e0 08          	shl    $0x8,%r8
    38ab:	48 8d 4e 20          	lea    0x20(%rsi),%rcx
    38af:	49 c1 e1 07          	shl    $0x7,%r9
    38b3:	49 01 c8             	add    %rcx,%r8
    38b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x].task_count;
    38c0:	89 f8                	mov    %edi,%eax
        data->threads[x].tasks[next].scheduled = 1;
    38c2:	48 8b 31             	mov    (%rcx),%rsi
        int next = (y + 1) % data->threads[x].task_count;
    38c5:	99                   	cltd
    38c6:	f7 79 08             	idivl  0x8(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    38c9:	48 81 c1 00 03 00 00 	add    $0x300,%rcx
        data->threads[x].tasks[next].scheduled = 1;
    38d0:	48 63 d2             	movslq %edx,%rdx
    38d3:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
    38d7:	48 8d 04 42          	lea    (%rdx,%rax,2),%rax
    38db:	48 c1 e0 07          	shl    $0x7,%rax
    38df:	c7 84 06 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rsi,%rax,1)
        data->threads[x].tasks[y].scheduled = 0;
    38ea:	42 c7 84 0e 00 03 00 00 00 00 00 00 	movl   $0x0,0x300(%rsi,%r9,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    38f6:	49 39 c8             	cmp    %rcx,%r8
    38f9:	75 c5                	jne    38c0 <timer_thread+0xc0>
    asm volatile ("mfence" ::: "memory");
    38fb:	0f ae f0             	mfence
    if (y >= data->threads[0].task_count) {
    38fe:	49 8b 47 10          	mov    0x10(%r15),%rax
  while (data->running && n < times) {
    3902:	41 8b 57 2c          	mov    0x2c(%r15),%edx
    y++;
    3906:	39 78 28             	cmp    %edi,0x28(%rax)
    3909:	0f 4e fb             	cmovle %ebx,%edi
    390c:	4c 63 ef             	movslq %edi,%r13
  while (data->running && n < times) {
    390f:	85 d2                	test   %edx,%edx
    3911:	74 0d                	je     3920 <timer_thread+0x120>
    3913:	41 81 fe 30 75 00 00 	cmp    $0x7530,%r14d
    391a:	0f 85 5a ff ff ff    	jne    387a <timer_thread+0x7a>
    3920:	48 8d 3d 11 27 00 00 	lea    0x2711(%rip),%rdi        # 6038 <_IO_stdin_used+0x38>
    3927:	e8 a4 e9 ff ff       	call   22d0 <puts@plt>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    392c:	49 63 57 1c          	movslq 0x1c(%r15),%rdx
    3930:	85 d2                	test   %edx,%edx
    3932:	7e 6e                	jle    39a2 <timer_thread+0x1a2>
    for (int y = 0 ; y < data->task_count ; y++) {
    3934:	49 63 47 28          	movslq 0x28(%r15),%rax
    3938:	85 c0                	test   %eax,%eax
    393a:	7e 66                	jle    39a2 <timer_thread+0x1a2>
    393c:	48 8d 3c 52          	lea    (%rdx,%rdx,2),%rdi
    3940:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
      data->threads[x].tasks[y].sending = 0;
    3944:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3948:	31 c9                	xor    %ecx,%ecx
    394a:	48 8d 34 50          	lea    (%rax,%rdx,2),%rsi
    394e:	48 c1 e7 08          	shl    $0x8,%rdi
    3952:	48 c1 e6 07          	shl    $0x7,%rsi
    for (int y = 0 ; y < data->task_count ; y++) {
    3956:	49 8b 44 08 20       	mov    0x20(%r8,%rcx,1),%rax
    395b:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    395f:	40 f6 c6 80          	test   $0x80,%sil
    3963:	74 15                	je     397a <timer_thread+0x17a>
      data->threads[x].tasks[y].sending = 0;
    3965:	c7 80 08 05 00 00 00 00 00 00 	movl   $0x0,0x508(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    396f:	48 05 80 05 00 00    	add    $0x580,%rax
    3975:	48 39 c2             	cmp    %rax,%rdx
    3978:	74 1c                	je     3996 <timer_thread+0x196>
      data->threads[x].tasks[y].sending = 0;
    397a:	c7 80 08 05 00 00 00 00 00 00 	movl   $0x0,0x508(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3984:	48 05 00 0b 00 00    	add    $0xb00,%rax
      data->threads[x].tasks[y].sending = 0;
    398a:	c7 40 88 00 00 00 00 	movl   $0x0,-0x78(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    3991:	48 39 c2             	cmp    %rax,%rdx
    3994:	75 e4                	jne    397a <timer_thread+0x17a>
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    3996:	48 81 c1 00 03 00 00 	add    $0x300,%rcx
    399d:	48 39 cf             	cmp    %rcx,%rdi
    39a0:	75 b4                	jne    3956 <timer_thread+0x156>
  asm volatile ("mfence" ::: "memory");
    39a2:	0f ae f0             	mfence
  struct timespec drain = {
    39a5:	66 0f 6f 05 53 2f 00 00 	movdqa 0x2f53(%rip),%xmm0        # 6900 <_IO_stdin_used+0x900>
    39ad:	48 8d 2d a9 26 00 00 	lea    0x26a9(%rip),%rbp        # 605d <_IO_stdin_used+0x5d>
    39b4:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    39b9:	49 63 47 18          	movslq 0x18(%r15),%rax
    y++;
    39bd:	41 8d 7d 01          	lea    0x1(%r13),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    39c1:	85 c0                	test   %eax,%eax
    39c3:	7e 66                	jle    3a2b <timer_thread+0x22b>
        data->threads[x].tasks[y].scheduled = 0;
    39c5:	4d 63 ed             	movslq %r13d,%r13
    39c8:	49 8b 5f 10          	mov    0x10(%r15),%rbx
    39cc:	4c 8d 04 40          	lea    (%rax,%rax,2),%r8
    39d0:	4b 8d 54 ad 00       	lea    0x0(%r13,%r13,4),%rdx
    39d5:	49 c1 e0 08          	shl    $0x8,%r8
    39d9:	4d 8d 4c 55 00       	lea    0x0(%r13,%rdx,2),%r9
    39de:	48 8d 4b 20          	lea    0x20(%rbx),%rcx
    39e2:	49 c1 e1 07          	shl    $0x7,%r9
    39e6:	49 01 c8             	add    %rcx,%r8
    39e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x].task_count;
    39f0:	89 f8                	mov    %edi,%eax
        data->threads[x].tasks[next].scheduled = 1;
    39f2:	48 8b 31             	mov    (%rcx),%rsi
        int next = (y + 1) % data->threads[x].task_count;
    39f5:	99                   	cltd
    39f6:	f7 79 08             	idivl  0x8(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    39f9:	48 81 c1 00 03 00 00 	add    $0x300,%rcx
        data->threads[x].tasks[next].scheduled = 1;
    3a00:	48 63 c2             	movslq %edx,%rax
    3a03:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3a07:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    3a0b:	48 c1 e0 07          	shl    $0x7,%rax
    3a0f:	c7 84 06 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rsi,%rax,1)
        data->threads[x].tasks[y].scheduled = 0;
    3a1a:	42 c7 84 0e 00 03 00 00 00 00 00 00 	movl   $0x0,0x300(%rsi,%r9,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a26:	4c 39 c1             	cmp    %r8,%rcx
    3a29:	75 c5                	jne    39f0 <timer_thread+0x1f0>
    asm volatile ("mfence" ::: "memory");
    3a2b:	0f ae f0             	mfence
    if (y >= data->threads[0].task_count) {
    3a2e:	49 8b 57 10          	mov    0x10(%r15),%rdx
    y++;
    3a32:	45 31 ed             	xor    %r13d,%r13d
    3a35:	39 7a 28             	cmp    %edi,0x28(%rdx)
    3a38:	44 0f 4f ef          	cmovg  %edi,%r13d
    for (int x = 0 ; x < data->thread_count ; x++) {
    3a3c:	41 8b 7f 18          	mov    0x18(%r15),%edi
    3a40:	85 ff                	test   %edi,%edi
    3a42:	0f 8e c3 00 00 00    	jle    3b0b <timer_thread+0x30b>
    3a48:	31 db                	xor    %ebx,%ebx
    3a4a:	45 31 e4             	xor    %r12d,%r12d
    3a4d:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    3a53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            all_empty = 0;
    3a58:	45 31 f6             	xor    %r14d,%r14d
    3a5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3a60:	4b 8d 04 b6          	lea    (%r14,%r14,4),%rax
    3a64:	49 8d 04 46          	lea    (%r14,%rax,2),%rax
    3a68:	48 c1 e0 07          	shl    $0x7,%rax
    3a6c:	48 03 44 1a 20       	add    0x20(%rdx,%rbx,1),%rax
        for (int k = 0 ; k < data->thread_count; k++) {
    3a71:	31 d2                	xor    %edx,%edx
    3a73:	48 8b 80 88 04 00 00 	mov    0x488(%rax),%rax
    3a7a:	eb 16                	jmp    3a92 <timer_thread+0x292>
    3a7c:	0f 1f 40 00          	nopl   0x0(%rax)
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3a80:	4d 85 c0             	test   %r8,%r8
    3a83:	7f 2a                	jg     3aaf <timer_thread+0x2af>
        for (int k = 0 ; k < data->thread_count; k++) {
    3a85:	83 c2 01             	add    $0x1,%edx
    3a88:	48 05 00 02 00 00    	add    $0x200,%rax
    3a8e:	39 fa                	cmp    %edi,%edx
    3a90:	74 33                	je     3ac5 <timer_thread+0x2c5>
          if (((struct Data*)data->threads[x].tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x].tasks[y].mailboxes[k].higher)->messages_count > 0) {
    3a92:	48 8b 08             	mov    (%rax),%rcx
    3a95:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
    3a9c:	48 8b 89 80 00 00 00 	mov    0x80(%rcx),%rcx
    3aa3:	4c 8b 86 80 00 00 00 	mov    0x80(%rsi),%r8
    3aaa:	48 85 c9             	test   %rcx,%rcx
    3aad:	7e d1                	jle    3a80 <timer_thread+0x280>
    3aaf:	bf 01 00 00 00       	mov    $0x1,%edi
    3ab4:	48 89 ee             	mov    %rbp,%rsi
    3ab7:	31 c0                	xor    %eax,%eax
    3ab9:	e8 72 e9 ff ff       	call   2430 <__printf_chk@plt>
            break;
    3abe:	41 8b 7f 18          	mov    0x18(%r15),%edi
            all_empty = 0;
    3ac2:	45 31 c9             	xor    %r9d,%r9d
      for (int y = 0 ; y < data->thread_count ; y++) {
    3ac5:	49 83 c6 01          	add    $0x1,%r14
    3ac9:	44 39 f7             	cmp    %r14d,%edi
    3acc:	7e 0a                	jle    3ad8 <timer_thread+0x2d8>
    3ace:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3ad2:	eb 8c                	jmp    3a60 <timer_thread+0x260>
    3ad4:	0f 1f 40 00          	nopl   0x0(%rax)
    for (int x = 0 ; x < data->thread_count ; x++) {
    3ad8:	41 83 c4 01          	add    $0x1,%r12d
    3adc:	48 81 c3 00 03 00 00 	add    $0x300,%rbx
    3ae3:	44 39 e7             	cmp    %r12d,%edi
    3ae6:	7e 09                	jle    3af1 <timer_thread+0x2f1>
    3ae8:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3aec:	e9 67 ff ff ff       	jmp    3a58 <timer_thread+0x258>
    if (all_empty == 1) {
    3af1:	41 83 f9 01          	cmp    $0x1,%r9d
    3af5:	74 14                	je     3b0b <timer_thread+0x30b>
      nanosleep(&drain , &drainrem);
    3af7:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3afc:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3b01:	e8 2a e8 ff ff       	call   2330 <nanosleep@plt>
    3b06:	e9 ae fe ff ff       	jmp    39b9 <timer_thread+0x1b9>
    3b0b:	48 8d 3d 42 25 00 00 	lea    0x2542(%rip),%rdi        # 6054 <_IO_stdin_used+0x54>
    3b12:	e8 b9 e7 ff ff       	call   22d0 <puts@plt>
  while (data->running) {
    3b17:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    3b1b:	85 c0                	test   %eax,%eax
    3b1d:	0f 84 d7 00 00 00    	je     3bfa <timer_thread+0x3fa>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b23:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3b27:	85 c9                	test   %ecx,%ecx
    3b29:	7e 3a                	jle    3b65 <timer_thread+0x365>
    3b2b:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3b2f:	31 db                	xor    %ebx,%ebx
    3b31:	4c 8d 25 36 25 00 00 	lea    0x2536(%rip),%r12        # 606e <_IO_stdin_used+0x6e>
    3b38:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      data->threads[x].running = 0;
    3b40:	48 8d 2c 5b          	lea    (%rbx,%rbx,2),%rbp
    3b44:	48 c1 e5 08          	shl    $0x8,%rbp
    3b48:	48 8d 04 2a          	lea    (%rdx,%rbp,1),%rax
      if (data->threads[x].type == IO) {
    3b4c:	83 78 04 02          	cmpl   $0x2,0x4(%rax)
      data->threads[x].running = 0;
    3b50:	c7 40 2c 00 00 00 00 	movl   $0x0,0x2c(%rax)
      if (data->threads[x].type == IO) {
    3b57:	0f 84 ca 00 00 00    	je     3c27 <timer_thread+0x427>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3b5d:	48 83 c3 01          	add    $0x1,%rbx
    3b61:	39 d9                	cmp    %ebx,%ecx
    3b63:	7f db                	jg     3b40 <timer_thread+0x340>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3b65:	49 63 57 18          	movslq 0x18(%r15),%rdx
    3b69:	85 d2                	test   %edx,%edx
    3b6b:	7e 76                	jle    3be3 <timer_thread+0x3e3>
      for (int y = 0 ; y < data->task_count ; y++) {
    3b6d:	49 63 47 28          	movslq 0x28(%r15),%rax
    3b71:	85 c0                	test   %eax,%eax
    3b73:	7e 6e                	jle    3be3 <timer_thread+0x3e3>
    3b75:	48 8d 3c 52          	lea    (%rdx,%rdx,2),%rdi
    3b79:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
        data->threads[x].tasks[y].scheduled = 0;
    3b7d:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3b81:	31 c9                	xor    %ecx,%ecx
    3b83:	48 8d 34 50          	lea    (%rax,%rdx,2),%rsi
    3b87:	48 c1 e7 08          	shl    $0x8,%rdi
    3b8b:	48 c1 e6 07          	shl    $0x7,%rsi
    3b8f:	90                   	nop
      for (int y = 0 ; y < data->task_count ; y++) {
    3b90:	49 8b 44 08 20       	mov    0x20(%r8,%rcx,1),%rax
    3b95:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3b99:	40 f6 c6 80          	test   $0x80,%sil
    3b9d:	74 19                	je     3bb8 <timer_thread+0x3b8>
        data->threads[x].tasks[y].scheduled = 0;
    3b9f:	c7 80 00 03 00 00 00 00 00 00 	movl   $0x0,0x300(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3ba9:	48 05 80 05 00 00    	add    $0x580,%rax
    3baf:	48 39 d0             	cmp    %rdx,%rax
    3bb2:	74 23                	je     3bd7 <timer_thread+0x3d7>
    3bb4:	0f 1f 40 00          	nopl   0x0(%rax)
        data->threads[x].tasks[y].scheduled = 0;
    3bb8:	c7 80 00 03 00 00 00 00 00 00 	movl   $0x0,0x300(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3bc2:	48 05 00 0b 00 00    	add    $0xb00,%rax
        data->threads[x].tasks[y].scheduled = 0;
    3bc8:	c7 80 80 fd ff ff 00 00 00 00 	movl   $0x0,-0x280(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    3bd2:	48 39 d0             	cmp    %rdx,%rax
    3bd5:	75 e1                	jne    3bb8 <timer_thread+0x3b8>
    for (int x = 0 ; x < data->thread_count ; x++) {
    3bd7:	48 81 c1 00 03 00 00 	add    $0x300,%rcx
    3bde:	48 39 f9             	cmp    %rdi,%rcx
    3be1:	75 ad                	jne    3b90 <timer_thread+0x390>
    asm volatile ("mfence" ::: "memory");
    3be3:	0f ae f0             	mfence
    3be6:	48 8d 3d 93 24 00 00 	lea    0x2493(%rip),%rdi        # 6080 <_IO_stdin_used+0x80>
    3bed:	e8 de e6 ff ff       	call   22d0 <puts@plt>
    data->running = 0;
    3bf2:	41 c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%r15)
    3bfa:	48 8d 3d 86 24 00 00 	lea    0x2486(%rip),%rdi        # 6087 <_IO_stdin_used+0x87>
    3c01:	e8 ca e6 ff ff       	call   22d0 <puts@plt>
}
    3c06:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3c0b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3c14:	75 44                	jne    3c5a <timer_thread+0x45a>
    3c16:	48 83 c4 58          	add    $0x58,%rsp
    3c1a:	31 c0                	xor    %eax,%eax
    3c1c:	5b                   	pop    %rbx
    3c1d:	5d                   	pop    %rbp
    3c1e:	41 5c                	pop    %r12
    3c20:	41 5d                	pop    %r13
    3c22:	41 5e                	pop    %r14
    3c24:	41 5f                	pop    %r15
    3c26:	c3                   	ret
    3c27:	4c 89 e7             	mov    %r12,%rdi
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c2a:	48 83 c3 01          	add    $0x1,%rbx
    3c2e:	e8 9d e6 ff ff       	call   22d0 <puts@plt>
        eventfd_write(data->threads[x]._eventfd, 1);
    3c33:	49 8b 47 10          	mov    0x10(%r15),%rax
    3c37:	be 01 00 00 00       	mov    $0x1,%esi
    3c3c:	8b 7c 28 48          	mov    0x48(%rax,%rbp,1),%edi
    3c40:	e8 9b e7 ff ff       	call   23e0 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    3c45:	41 8b 4f 1c          	mov    0x1c(%r15),%ecx
    3c49:	39 d9                	cmp    %ebx,%ecx
    3c4b:	0f 8e 14 ff ff ff    	jle    3b65 <timer_thread+0x365>
    3c51:	49 8b 57 10          	mov    0x10(%r15),%rdx
    3c55:	e9 e6 fe ff ff       	jmp    3b40 <timer_thread+0x340>
}
    3c5a:	e8 b1 e6 ff ff       	call   2310 <__stack_chk_fail@plt>
    3c5f:	90                   	nop

0000000000003c60 <strtolower>:
void strtolower(char *str) {
    3c60:	f3 0f 1e fa          	endbr64
    3c64:	55                   	push   %rbp
    3c65:	53                   	push   %rbx
    3c66:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    3c6a:	48 0f be 1f          	movsbq (%rdi),%rbx
    3c6e:	84 db                	test   %bl,%bl
    3c70:	74 24                	je     3c96 <strtolower+0x36>
    3c72:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    3c75:	e8 76 e8 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3c7a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3c80:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    3c83:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    3c87:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3c8a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    3c8d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3c92:	84 db                	test   %bl,%bl
    3c94:	75 ea                	jne    3c80 <strtolower+0x20>
}
    3c96:	48 83 c4 08          	add    $0x8,%rsp
    3c9a:	5b                   	pop    %rbx
    3c9b:	5d                   	pop    %rbp
    3c9c:	c3                   	ret
    3c9d:	0f 1f 00             	nopl   (%rax)

0000000000003ca0 <zh_malloc>:
void *zh_malloc(size_t size) {
    3ca0:	f3 0f 1e fa          	endbr64
    3ca4:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    3ca8:	e8 43 e7 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3cad:	48 85 c0             	test   %rax,%rax
    3cb0:	74 05                	je     3cb7 <zh_malloc+0x17>
}
    3cb2:	48 83 c4 08          	add    $0x8,%rsp
    3cb6:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3cb7:	48 8b 0d 62 53 00 00 	mov    0x5362(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    3cbe:	ba 28 00 00 00       	mov    $0x28,%edx
    3cc3:	be 01 00 00 00       	mov    $0x1,%esi
    3cc8:	48 8d 3d 51 27 00 00 	lea    0x2751(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    3ccf:	e8 cc e7 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    3cd4:	bf 01 00 00 00       	mov    $0x1,%edi
    3cd9:	e8 a2 e7 ff ff       	call   2480 <exit@plt>
    3cde:	66 90                	xchg   %ax,%ax

0000000000003ce0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    3ce0:	f3 0f 1e fa          	endbr64
    3ce4:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    3ce5:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    3cea:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    3ced:	e8 4e e6 ff ff       	call   2340 <strrchr@plt>
    if (!dot || dot == filename)
    3cf2:	48 85 c0             	test   %rax,%rax
    3cf5:	74 11                	je     3d08 <get_filename_ext+0x28>
    3cf7:	48 39 c3             	cmp    %rax,%rbx
    3cfa:	74 0c                	je     3d08 <get_filename_ext+0x28>
    return dot + 1;
    3cfc:	48 83 c0 01          	add    $0x1,%rax
}
    3d00:	5b                   	pop    %rbx
    3d01:	c3                   	ret
    3d02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    3d08:	48 8d 05 c0 23 00 00 	lea    0x23c0(%rip),%rax        # 60cf <_IO_stdin_used+0xcf>
}
    3d0f:	5b                   	pop    %rbx
    3d10:	c3                   	ret
    3d11:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3d1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003d20 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    3d20:	f3 0f 1e fa          	endbr64
    3d24:	41 55                	push   %r13
    3d26:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3d29:	48 89 fe             	mov    %rdi,%rsi
    3d2c:	41 54                	push   %r12
    3d2e:	55                   	push   %rbp
    3d2f:	48 89 d5             	mov    %rdx,%rbp
    3d32:	ba 00 04 00 00       	mov    $0x400,%edx
    3d37:	53                   	push   %rbx
    3d38:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    3d3f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3d48:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3d50:	31 c0                	xor    %eax,%eax
    3d52:	49 89 e4             	mov    %rsp,%r12
    3d55:	4c 89 e7             	mov    %r12,%rdi
    3d58:	e8 b3 e6 ff ff       	call   2410 <__strcpy_chk@plt>
    for (; *str; ++str)
    3d5d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3d62:	84 db                	test   %bl,%bl
    3d64:	74 24                	je     3d8a <send_headers+0x6a>
        *str = (char)tolower(*str);
    3d66:	e8 85 e7 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3d6b:	48 8b 08             	mov    (%rax),%rcx
    3d6e:	4c 89 e0             	mov    %r12,%rax
    3d71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3d78:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    3d7b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    3d7f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    3d82:	48 0f be 18          	movsbq (%rax),%rbx
    3d86:	84 db                	test   %bl,%bl
    3d88:	75 ee                	jne    3d78 <send_headers+0x58>
    void *buf = malloc(size);
    3d8a:	bf 11 00 00 00       	mov    $0x11,%edi
    3d8f:	e8 5c e6 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3d94:	48 85 c0             	test   %rax,%rax
    3d97:	0f 84 7e 04 00 00    	je     421b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3d9d:	66 0f 6f 05 6b 2b 00 00 	movdqa 0x2b6b(%rip),%xmm0        # 6910 <_IO_stdin_used+0x910>
    iov[0].iov_base = zh_malloc(slen);
    3da5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    3da9:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    3dae:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3db6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3dba:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    3dbd:	e8 2e e6 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3dc2:	48 85 c0             	test   %rax,%rax
    3dc5:	0f 84 50 04 00 00    	je     421b <send_headers+0x4fb>
    3dcb:	66 0f 6f 05 4d 2b 00 00 	movdqa 0x2b4d(%rip),%xmm0        # 6920 <_IO_stdin_used+0x920>
    iov[1].iov_base = zh_malloc(slen);
    3dd3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    3dd7:	4c 89 e7             	mov    %r12,%rdi
    3dda:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    3de4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    3dec:	0f 11 00             	movups %xmm0,(%rax)
    3def:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    3df3:	be 2e 00 00 00       	mov    $0x2e,%esi
    3df8:	e8 43 e5 ff ff       	call   2340 <strrchr@plt>
    if (!dot || dot == filename)
    3dfd:	48 85 c0             	test   %rax,%rax
    3e00:	0f 84 ea 02 00 00    	je     40f0 <send_headers+0x3d0>
    3e06:	4c 39 e0             	cmp    %r12,%rax
    3e09:	0f 84 e1 02 00 00    	je     40f0 <send_headers+0x3d0>
    return dot + 1;
    3e0f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    3e13:	48 8d 3d 83 22 00 00 	lea    0x2283(%rip),%rdi        # 609d <_IO_stdin_used+0x9d>
    3e1a:	48 89 de             	mov    %rbx,%rsi
    3e1d:	e8 6e e5 ff ff       	call   2390 <strcmp@plt>
    3e22:	85 c0                	test   %eax,%eax
    3e24:	75 20                	jne    3e46 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3e26:	66 0f 6f 05 02 2b 00 00 	movdqa 0x2b02(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3e2e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3e36:	66 0f 6f 05 02 2b 00 00 	movdqa 0x2b02(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3e3e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    3e46:	48 89 de             	mov    %rbx,%rsi
    3e49:	48 8d 3d 51 22 00 00 	lea    0x2251(%rip),%rdi        # 60a1 <_IO_stdin_used+0xa1>
    3e50:	e8 3b e5 ff ff       	call   2390 <strcmp@plt>
    3e55:	85 c0                	test   %eax,%eax
    3e57:	75 20                	jne    3e79 <send_headers+0x159>
    3e59:	66 0f 6f 05 cf 2a 00 00 	movdqa 0x2acf(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3e61:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3e69:	66 0f 6f 05 cf 2a 00 00 	movdqa 0x2acf(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3e71:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    3e79:	48 89 de             	mov    %rbx,%rsi
    3e7c:	48 8d 3d 23 22 00 00 	lea    0x2223(%rip),%rdi        # 60a6 <_IO_stdin_used+0xa6>
    3e83:	e8 08 e5 ff ff       	call   2390 <strcmp@plt>
    3e88:	85 c0                	test   %eax,%eax
    3e8a:	0f 84 10 02 00 00    	je     40a0 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    3e90:	48 89 de             	mov    %rbx,%rsi
    3e93:	48 8d 3d 10 22 00 00 	lea    0x2210(%rip),%rdi        # 60aa <_IO_stdin_used+0xaa>
    3e9a:	e8 f1 e4 ff ff       	call   2390 <strcmp@plt>
    3e9f:	85 c0                	test   %eax,%eax
    3ea1:	0f 84 a9 02 00 00    	je     4150 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    3ea7:	48 89 de             	mov    %rbx,%rsi
    3eaa:	48 8d 3d fd 21 00 00 	lea    0x21fd(%rip),%rdi        # 60ae <_IO_stdin_used+0xae>
    3eb1:	e8 da e4 ff ff       	call   2390 <strcmp@plt>
    3eb6:	85 c0                	test   %eax,%eax
    3eb8:	0f 84 6a 02 00 00    	je     4128 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    3ebe:	48 89 de             	mov    %rbx,%rsi
    3ec1:	48 8d 3d 29 22 00 00 	lea    0x2229(%rip),%rdi        # 60f1 <_IO_stdin_used+0xf1>
    3ec8:	e8 c3 e4 ff ff       	call   2390 <strcmp@plt>
    3ecd:	85 c0                	test   %eax,%eax
    3ecf:	0f 84 2b 02 00 00    	je     4100 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    3ed5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3ed8:	0f 84 52 01 00 00    	je     4030 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    3ede:	48 89 de             	mov    %rbx,%rsi
    3ee1:	48 8d 3d ca 21 00 00 	lea    0x21ca(%rip),%rdi        # 60b2 <_IO_stdin_used+0xb2>
    3ee8:	e8 a3 e4 ff ff       	call   2390 <strcmp@plt>
    3eed:	85 c0                	test   %eax,%eax
    3eef:	0f 84 ab 02 00 00    	je     41a0 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    3ef5:	48 89 de             	mov    %rbx,%rsi
    3ef8:	48 8d 3d b7 21 00 00 	lea    0x21b7(%rip),%rdi        # 60b6 <_IO_stdin_used+0xb6>
    3eff:	e8 8c e4 ff ff       	call   2390 <strcmp@plt>
    3f04:	85 c0                	test   %eax,%eax
    3f06:	0f 84 6c 02 00 00    	je     4178 <send_headers+0x458>
    slen = strlen(send_buffer);
    3f0c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    3f14:	4c 89 e7             	mov    %r12,%rdi
    3f17:	e8 e4 e3 ff ff       	call   2300 <strlen@plt>
    void *buf = malloc(size);
    3f1c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3f1f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    3f22:	e8 c9 e4 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3f27:	48 85 c0             	test   %rax,%rax
    3f2a:	0f 84 eb 02 00 00    	je     421b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    3f30:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    3f34:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    3f38:	83 fb 08             	cmp    $0x8,%ebx
    3f3b:	0f 83 3f 01 00 00    	jae    4080 <send_headers+0x360>
    3f41:	f6 c3 04             	test   $0x4,%bl
    3f44:	0f 85 7b 02 00 00    	jne    41c5 <send_headers+0x4a5>
    3f4a:	85 db                	test   %ebx,%ebx
    3f4c:	74 13                	je     3f61 <send_headers+0x241>
    3f4e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3f56:	88 10                	mov    %dl,(%rax)
    3f58:	f6 c3 02             	test   $0x2,%bl
    3f5b:	0f 85 96 02 00 00    	jne    41f7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3f61:	4d 89 e8             	mov    %r13,%r8
    3f64:	48 8d 0d 4f 21 00 00 	lea    0x214f(%rip),%rcx        # 60ba <_IO_stdin_used+0xba>
    3f6b:	4c 89 e7             	mov    %r12,%rdi
    3f6e:	31 c0                	xor    %eax,%eax
    3f70:	ba 00 04 00 00       	mov    $0x400,%edx
    3f75:	be 01 00 00 00       	mov    $0x1,%esi
    3f7a:	e8 81 e5 ff ff       	call   2500 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    3f7f:	4c 89 e7             	mov    %r12,%rdi
    3f82:	e8 79 e3 ff ff       	call   2300 <strlen@plt>
    void *buf = malloc(size);
    3f87:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    3f8a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    3f8d:	e8 5e e4 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3f92:	48 85 c0             	test   %rax,%rax
    3f95:	0f 84 80 02 00 00    	je     421b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    3f9b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    3f9f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    3fa3:	83 fb 08             	cmp    $0x8,%ebx
    3fa6:	0f 83 1c 01 00 00    	jae    40c8 <send_headers+0x3a8>
    3fac:	f6 c3 04             	test   $0x4,%bl
    3faf:	0f 85 29 02 00 00    	jne    41de <send_headers+0x4be>
    3fb5:	85 db                	test   %ebx,%ebx
    3fb7:	74 13                	je     3fcc <send_headers+0x2ac>
    3fb9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3fc1:	88 10                	mov    %dl,(%rax)
    3fc3:	f6 c3 02             	test   $0x2,%bl
    3fc6:	0f 85 3d 02 00 00    	jne    4209 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    3fcc:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    3fd1:	bf 02 00 00 00       	mov    $0x2,%edi
    3fd6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    3fde:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    3fe6:	e8 05 e4 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    3feb:	48 85 c0             	test   %rax,%rax
    3fee:	0f 84 27 02 00 00    	je     421b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    3ff4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    3ffc:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4000:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4008:	66 89 10             	mov    %dx,(%rax)
}
    400b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4013:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    401c:	0f 85 20 02 00 00    	jne    4242 <send_headers+0x522>
    4022:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4029:	5b                   	pop    %rbx
    402a:	5d                   	pop    %rbp
    402b:	41 5c                	pop    %r12
    402d:	41 5d                	pop    %r13
    402f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4030:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4034:	0f 85 a4 fe ff ff    	jne    3ede <send_headers+0x1be>
    403a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    403e:	0f 85 9a fe ff ff    	jne    3ede <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4044:	66 0f 6f 05 44 29 00 00 	movdqa 0x2944(%rip),%xmm0        # 6990 <_IO_stdin_used+0x990>
    404c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4056:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    405e:	66 0f 6f 05 3a 29 00 00 	movdqa 0x293a(%rip),%xmm0        # 69a0 <_IO_stdin_used+0x9a0>
    4066:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    406e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4076:	e9 63 fe ff ff       	jmp    3ede <send_headers+0x1be>
    407b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4080:	89 da                	mov    %ebx,%edx
    4082:	48 89 c7             	mov    %rax,%rdi
    4085:	4c 89 e6             	mov    %r12,%rsi
    4088:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    408d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4092:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4095:	c1 e9 03             	shr    $0x3,%ecx
    4098:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    409b:	e9 c1 fe ff ff       	jmp    3f61 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    40a0:	66 0f 6f 05 88 28 00 00 	movdqa 0x2888(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    40a8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40b0:	66 0f 6f 05 98 28 00 00 	movdqa 0x2898(%rip),%xmm0        # 6950 <_IO_stdin_used+0x950>
    40b8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    40c0:	e9 cb fd ff ff       	jmp    3e90 <send_headers+0x170>
    40c5:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    40c8:	89 da                	mov    %ebx,%edx
    40ca:	48 89 c7             	mov    %rax,%rdi
    40cd:	4c 89 e6             	mov    %r12,%rsi
    40d0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    40d5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    40da:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    40dd:	c1 e9 03             	shr    $0x3,%ecx
    40e0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    40e3:	e9 e4 fe ff ff       	jmp    3fcc <send_headers+0x2ac>
    40e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    40f0:	48 8d 1d d8 1f 00 00 	lea    0x1fd8(%rip),%rbx        # 60cf <_IO_stdin_used+0xcf>
    40f7:	e9 94 fd ff ff       	jmp    3e90 <send_headers+0x170>
    40fc:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4100:	66 0f 6f 05 68 28 00 00 	movdqa 0x2868(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4108:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4110:	66 0f 6f 05 68 28 00 00 	movdqa 0x2868(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    4118:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4120:	e9 b0 fd ff ff       	jmp    3ed5 <send_headers+0x1b5>
    4125:	0f 1f 00             	nopl   (%rax)
    4128:	66 0f 6f 05 40 28 00 00 	movdqa 0x2840(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4130:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4138:	66 0f 6f 05 40 28 00 00 	movdqa 0x2840(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    4140:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4148:	e9 71 fd ff ff       	jmp    3ebe <send_headers+0x19e>
    414d:	0f 1f 00             	nopl   (%rax)
    4150:	66 0f 6f 05 d8 27 00 00 	movdqa 0x27d8(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    4158:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4160:	66 0f 6f 05 f8 27 00 00 	movdqa 0x27f8(%rip),%xmm0        # 6960 <_IO_stdin_used+0x960>
    4168:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4170:	e9 32 fd ff ff       	jmp    3ea7 <send_headers+0x187>
    4175:	0f 1f 00             	nopl   (%rax)
    4178:	66 0f 6f 05 f0 27 00 00 	movdqa 0x27f0(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4180:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4188:	66 0f 6f 05 30 28 00 00 	movdqa 0x2830(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    4190:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4198:	e9 6f fd ff ff       	jmp    3f0c <send_headers+0x1ec>
    419d:	0f 1f 00             	nopl   (%rax)
    41a0:	66 0f 6f 05 c8 27 00 00 	movdqa 0x27c8(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    41a8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    41b0:	66 0f 6f 05 f8 27 00 00 	movdqa 0x27f8(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    41b8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    41c0:	e9 30 fd ff ff       	jmp    3ef5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    41c5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    41cc:	89 db                	mov    %ebx,%ebx
    41ce:	89 10                	mov    %edx,(%rax)
    41d0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    41d5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    41d9:	e9 83 fd ff ff       	jmp    3f61 <send_headers+0x241>
    41de:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    41e5:	89 db                	mov    %ebx,%ebx
    41e7:	89 10                	mov    %edx,(%rax)
    41e9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    41ee:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    41f2:	e9 d5 fd ff ff       	jmp    3fcc <send_headers+0x2ac>
    41f7:	89 db                	mov    %ebx,%ebx
    41f9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    41ff:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4204:	e9 58 fd ff ff       	jmp    3f61 <send_headers+0x241>
    4209:	89 db                	mov    %ebx,%ebx
    420b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4211:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4216:	e9 b1 fd ff ff       	jmp    3fcc <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    421b:	48 8b 0d fe 4d 00 00 	mov    0x4dfe(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4222:	ba 28 00 00 00       	mov    $0x28,%edx
    4227:	be 01 00 00 00       	mov    $0x1,%esi
    422c:	48 8d 3d ed 21 00 00 	lea    0x21ed(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    4233:	e8 68 e2 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    4238:	bf 01 00 00 00       	mov    $0x1,%edi
    423d:	e8 3e e2 ff ff       	call   2480 <exit@plt>
}
    4242:	e8 c9 e0 ff ff       	call   2310 <__stack_chk_fail@plt>
    4247:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004250 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4250:	f3 0f 1e fa          	endbr64
    4254:	41 55                	push   %r13
    4256:	49 89 d5             	mov    %rdx,%r13
    4259:	41 54                	push   %r12
    425b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    425e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4261:	55                   	push   %rbp
    4262:	53                   	push   %rbx
    4263:	48 89 f3             	mov    %rsi,%rbx
    4266:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    426a:	e8 81 e1 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    426f:	48 85 c0             	test   %rax,%rax
    4272:	74 6b                	je     42df <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4274:	4c 89 e7             	mov    %r12,%rdi
    4277:	48 89 c5             	mov    %rax,%rbp
    427a:	31 f6                	xor    %esi,%esi
    427c:	31 c0                	xor    %eax,%eax
    427e:	e8 dd e1 ff ff       	call   2460 <open@plt>
    4283:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4286:	85 c0                	test   %eax,%eax
    4288:	0f 88 a8 e2 ff ff    	js     2536 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    428e:	48 89 da             	mov    %rbx,%rdx
    4291:	48 89 ee             	mov    %rbp,%rsi
    4294:	89 c7                	mov    %eax,%edi
    4296:	e8 d5 e0 ff ff       	call   2370 <read@plt>
    if (ret < file_size) {
    429b:	48 98                	cltq
    429d:	48 39 d8             	cmp    %rbx,%rax
    42a0:	7c 1e                	jl     42c0 <copy_file_contents+0x70>
    close(fd);
    42a2:	44 89 e7             	mov    %r12d,%edi
    42a5:	e8 a6 e0 ff ff       	call   2350 <close@plt>
    iov->iov_base = buf;
    42aa:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    42ae:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    42b2:	48 83 c4 08          	add    $0x8,%rsp
    42b6:	5b                   	pop    %rbx
    42b7:	5d                   	pop    %rbp
    42b8:	41 5c                	pop    %r12
    42ba:	41 5d                	pop    %r13
    42bc:	c3                   	ret
    42bd:	0f 1f 00             	nopl   (%rax)
    42c0:	48 8b 0d 59 4d 00 00 	mov    0x4d59(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    42c7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    42cc:	be 01 00 00 00       	mov    $0x1,%esi
    42d1:	48 8d 3d f8 1d 00 00 	lea    0x1df8(%rip),%rdi        # 60d0 <_IO_stdin_used+0xd0>
    42d8:	e8 c3 e1 ff ff       	call   24a0 <fwrite@plt>
    42dd:	eb c3                	jmp    42a2 <copy_file_contents+0x52>
    42df:	48 8b 0d 3a 4d 00 00 	mov    0x4d3a(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    42e6:	ba 28 00 00 00       	mov    $0x28,%edx
    42eb:	be 01 00 00 00       	mov    $0x1,%esi
    42f0:	48 8d 3d 29 21 00 00 	lea    0x2129(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    42f7:	e8 a4 e1 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    42fc:	bf 01 00 00 00       	mov    $0x1,%edi
    4301:	e8 7a e1 ff ff       	call   2480 <exit@plt>
    4306:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004310 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    4310:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    4314:	8b 46 44             	mov    0x44(%rsi),%eax
    4317:	48 89 fa             	mov    %rdi,%rdx
    431a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    431d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4323:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    4326:	48 8b 07             	mov    (%rdi),%rax
    4329:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    432c:	f6 c1 02             	test   $0x2,%cl
    432f:	74 00                	je     4331 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    4331:	89 f0                	mov    %esi,%eax
    4333:	44 29 c0             	sub    %r8d,%eax
    4336:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4339:	0f 82 03 e2 ff ff    	jb     2542 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    433f:	c1 e9 0a             	shr    $0xa,%ecx
    4342:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4346:	8b 47 44             	mov    0x44(%rdi),%eax
    4349:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    434c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    434f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    4352:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    4355:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4359:	d3 e0                	shl    %cl,%eax
    435b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    435e:	48 c1 e0 06          	shl    $0x6,%rax
    4362:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    4366:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    436c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    436f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    4373:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4379:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4381:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    4385:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    4388:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    438f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4397:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    439b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    439f:	e8 7c df ff ff       	call   2320 <io_uring_submit@plt>
}
    43a4:	31 c0                	xor    %eax,%eax
    43a6:	48 83 c4 08          	add    $0x8,%rsp
    43aa:	c3                   	ret
    43ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000043b0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    43b0:	f3 0f 1e fa          	endbr64
    43b4:	41 55                	push   %r13
    43b6:	41 89 fd             	mov    %edi,%r13d
    43b9:	41 54                	push   %r12
    43bb:	55                   	push   %rbp
    43bc:	53                   	push   %rbx
    43bd:	48 89 f3             	mov    %rsi,%rbx
    43c0:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    43c4:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    43c7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    43cd:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    43d0:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    43d3:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    43d5:	f6 c1 02             	test   $0x2,%cl
    43d8:	74 00                	je     43da <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    43da:	89 c2                	mov    %eax,%edx
    43dc:	29 f2                	sub    %esi,%edx
    43de:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    43e1:	0f 82 6b e1 ff ff    	jb     2552 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    43e7:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    43ea:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    43ed:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    43f0:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    43f5:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    43f8:	23 6b 58             	and    0x58(%rbx),%ebp
    43fb:	d3 e5                	shl    %cl,%ebp
    43fd:	48 c1 e5 06          	shl    $0x6,%rbp
    4401:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4405:	e8 e6 df ff ff       	call   23f0 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    440a:	be 01 00 00 00       	mov    $0x1,%esi
    440f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    4414:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    4417:	e8 64 df ff ff       	call   2380 <calloc@plt>
    req->client_socket = client_socket;
    441c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    4421:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    4425:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    4428:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    442d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    4432:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    443b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    4443:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    4447:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    444b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    4452:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    445a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    445e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    4466:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    446e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    4472:	e8 a9 de ff ff       	call   2320 <io_uring_submit@plt>
}
    4477:	48 83 c4 08          	add    $0x8,%rsp
    447b:	31 c0                	xor    %eax,%eax
    447d:	5b                   	pop    %rbx
    447e:	5d                   	pop    %rbp
    447f:	41 5c                	pop    %r12
    4481:	41 5d                	pop    %r13
    4483:	c3                   	ret
    4484:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    448f:	90                   	nop

0000000000004490 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    4490:	f3 0f 1e fa          	endbr64
    4494:	41 56                	push   %r14
    4496:	41 89 f6             	mov    %esi,%r14d
    4499:	41 55                	push   %r13
    449b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    449e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    44a3:	41 54                	push   %r12
    44a5:	55                   	push   %rbp
    44a6:	48 89 d5             	mov    %rdx,%rbp
    44a9:	53                   	push   %rbx
    void *buf = malloc(size);
    44aa:	e8 41 df ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    44af:	48 85 c0             	test   %rax,%rax
    44b2:	0f 84 dd 00 00 00    	je     4595 <_send_static_string_content+0x105>
    44b8:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    44bb:	4c 89 ef             	mov    %r13,%rdi
    44be:	e8 3d de ff ff       	call   2300 <strlen@plt>
    req->iovec_count = 1;
    44c3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    44ca:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    44ce:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    44d1:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    44d4:	e8 17 df ff ff       	call   23f0 <malloc@plt>
    44d9:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    44dc:	48 85 c0             	test   %rax,%rax
    44df:	0f 84 b0 00 00 00    	je     4595 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    44e5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    44e9:	4c 89 e2             	mov    %r12,%rdx
    44ec:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    44ef:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    44f3:	e8 c8 de ff ff       	call   23c0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    44f8:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    44fb:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4501:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4504:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4508:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    450a:	f6 c1 02             	test   $0x2,%cl
    450d:	0f 85 7d 00 00 00    	jne    4590 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    4513:	89 d0                	mov    %edx,%eax
    4515:	29 f0                	sub    %esi,%eax
    4517:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    451a:	0f 82 3c e0 ff ff    	jb     255c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4520:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4523:	8b 45 44             	mov    0x44(%rbp),%eax
    4526:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    4529:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    452c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    452f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    4532:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    4538:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    453c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    453e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    4541:	48 89 ef             	mov    %rbp,%rdi
    4544:	48 c1 e0 06          	shl    $0x6,%rax
    4548:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    454c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    454f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    4553:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    4559:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4561:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    4565:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    4568:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    456f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4577:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    457b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    457f:	5b                   	pop    %rbx
    4580:	5d                   	pop    %rbp
    4581:	41 5c                	pop    %r12
    4583:	41 5d                	pop    %r13
    4585:	41 5e                	pop    %r14
    io_uring_submit(ring);
    4587:	e9 94 dd ff ff       	jmp    2320 <io_uring_submit@plt>
    458c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    4590:	e9 7e ff ff ff       	jmp    4513 <_send_static_string_content+0x83>
    4595:	48 8b 0d 84 4a 00 00 	mov    0x4a84(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    459c:	ba 28 00 00 00       	mov    $0x28,%edx
    45a1:	be 01 00 00 00       	mov    $0x1,%esi
    45a6:	48 8d 3d 73 1e 00 00 	lea    0x1e73(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    45ad:	e8 ee de ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    45b2:	bf 01 00 00 00       	mov    $0x1,%edi
    45b7:	e8 c4 de ff ff       	call   2480 <exit@plt>
    45bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000045c0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    45c0:	f3 0f 1e fa          	endbr64
    45c4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    45c7:	89 fe                	mov    %edi,%esi
    45c9:	48 8b 3d 48 4a 00 00 	mov    0x4a48(%rip),%rdi        # 9018 <unimplemented_content>
    45d0:	e9 bb fe ff ff       	jmp    4490 <_send_static_string_content>
    45d5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000045e0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    45e0:	f3 0f 1e fa          	endbr64
    45e4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    45e7:	89 fe                	mov    %edi,%esi
    45e9:	48 8b 3d 20 4a 00 00 	mov    0x4a20(%rip),%rdi        # 9010 <http_404_content>
    45f0:	e9 9b fe ff ff       	jmp    4490 <_send_static_string_content>
    45f5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004600 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    4600:	f3 0f 1e fa          	endbr64
    4604:	41 56                	push   %r14
    4606:	41 55                	push   %r13
    4608:	49 89 d5             	mov    %rdx,%r13
    460b:	41 54                	push   %r12
    460d:	41 89 f4             	mov    %esi,%r12d
    4610:	55                   	push   %rbp
    4611:	48 89 fd             	mov    %rdi,%rbp
    4614:	53                   	push   %rbx
    4615:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    461c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4625:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    462d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    462f:	e8 cc dc ff ff       	call   2300 <strlen@plt>
    4634:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4639:	48 89 c3             	mov    %rax,%rbx
    463c:	0f 84 b6 00 00 00    	je     46f8 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4642:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4647:	48 89 ee             	mov    %rbp,%rsi
    464a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    464e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4653:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    465b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4663:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    466e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4676:	e8 25 dd ff ff       	call   23a0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    467b:	48 89 e6             	mov    %rsp,%rsi
    467e:	4c 89 f7             	mov    %r14,%rdi
    4681:	e8 2a dd ff ff       	call   23b0 <stat@plt>
    4686:	83 f8 ff             	cmp    $0xffffffff,%eax
    4689:	0f 84 d3 00 00 00    	je     4762 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    468f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4693:	25 00 f0 00 00       	and    $0xf000,%eax
    4698:	3d 00 80 00 00       	cmp    $0x8000,%eax
    469d:	0f 84 f5 00 00 00    	je     4798 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    46a3:	48 8b 3d 66 49 00 00 	mov    0x4966(%rip),%rdi        # 9010 <http_404_content>
    46aa:	4c 89 ea             	mov    %r13,%rdx
    46ad:	44 89 e6             	mov    %r12d,%esi
    46b0:	e8 db fd ff ff       	call   4490 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    46b5:	4c 89 f2             	mov    %r14,%rdx
    46b8:	bf 01 00 00 00       	mov    $0x1,%edi
    46bd:	31 c0                	xor    %eax,%eax
    46bf:	48 8d 35 5a 1a 00 00 	lea    0x1a5a(%rip),%rsi        # 6120 <_IO_stdin_used+0x120>
    46c6:	e8 65 dd ff ff       	call   2430 <__printf_chk@plt>
}
    46cb:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    46d3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    46dc:	0f 85 20 01 00 00    	jne    4802 <handle_get_method+0x202>
    46e2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    46e9:	5b                   	pop    %rbx
    46ea:	5d                   	pop    %rbp
    46eb:	41 5c                	pop    %r12
    46ed:	41 5d                	pop    %r13
    46ef:	41 5e                	pop    %r14
    46f1:	c3                   	ret
    46f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    46f8:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    46fd:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4705:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    470a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    470d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    4715:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4718:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4720:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    472b:	e8 70 dc ff ff       	call   23a0 <__memcpy_chk@plt>
    4730:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4735:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    473a:	48 8d 35 aa 19 00 00 	lea    0x19aa(%rip),%rsi        # 60eb <_IO_stdin_used+0xeb>
    4741:	48 29 d9             	sub    %rbx,%rcx
    4744:	ba 0b 00 00 00       	mov    $0xb,%edx
    4749:	e8 52 dc ff ff       	call   23a0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    474e:	48 89 e6             	mov    %rsp,%rsi
    4751:	4c 89 f7             	mov    %r14,%rdi
    4754:	e8 57 dc ff ff       	call   23b0 <stat@plt>
    4759:	83 f8 ff             	cmp    $0xffffffff,%eax
    475c:	0f 85 2d ff ff ff    	jne    468f <handle_get_method+0x8f>
    4762:	4c 89 f2             	mov    %r14,%rdx
    4765:	48 89 e9             	mov    %rbp,%rcx
    4768:	48 8d 35 87 19 00 00 	lea    0x1987(%rip),%rsi        # 60f6 <_IO_stdin_used+0xf6>
    476f:	31 c0                	xor    %eax,%eax
    4771:	bf 01 00 00 00       	mov    $0x1,%edi
    4776:	e8 b5 dc ff ff       	call   2430 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    477b:	48 8b 3d 8e 48 00 00 	mov    0x488e(%rip),%rdi        # 9010 <http_404_content>
    4782:	4c 89 ea             	mov    %r13,%rdx
    4785:	44 89 e6             	mov    %r12d,%esi
    4788:	e8 03 fd ff ff       	call   4490 <_send_static_string_content>
}
    478d:	e9 39 ff ff ff       	jmp    46cb <handle_get_method+0xcb>
    4792:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    4798:	bf 70 00 00 00       	mov    $0x70,%edi
    479d:	e8 4e dc ff ff       	call   23f0 <malloc@plt>
    47a2:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    47a5:	48 85 c0             	test   %rax,%rax
    47a8:	74 5d                	je     4807 <handle_get_method+0x207>
            req->client_socket = client_socket;
    47aa:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    47ae:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    47b3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    47b7:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    47ba:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    47c1:	e8 5a f5 ff ff       	call   3d20 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    47c6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    47cb:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    47cf:	4c 89 f7             	mov    %r14,%rdi
    47d2:	e8 79 fa ff ff       	call   4250 <copy_file_contents>
    47d7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    47dc:	4c 89 f2             	mov    %r14,%rdx
    47df:	31 c0                	xor    %eax,%eax
    47e1:	48 8d 35 26 19 00 00 	lea    0x1926(%rip),%rsi        # 610e <_IO_stdin_used+0x10e>
    47e8:	bf 01 00 00 00       	mov    $0x1,%edi
    47ed:	e8 3e dc ff ff       	call   2430 <__printf_chk@plt>
            add_write_request(req, ring);
    47f2:	4c 89 ee             	mov    %r13,%rsi
    47f5:	48 89 df             	mov    %rbx,%rdi
    47f8:	e8 13 fb ff ff       	call   4310 <add_write_request>
    47fd:	e9 c9 fe ff ff       	jmp    46cb <handle_get_method+0xcb>
}
    4802:	e8 09 db ff ff       	call   2310 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4807:	48 8b 0d 12 48 00 00 	mov    0x4812(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    480e:	ba 28 00 00 00       	mov    $0x28,%edx
    4813:	be 01 00 00 00       	mov    $0x1,%esi
    4818:	48 8d 3d 01 1c 00 00 	lea    0x1c01(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    481f:	e8 7c dc ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    4824:	bf 01 00 00 00       	mov    $0x1,%edi
    4829:	e8 52 dc ff ff       	call   2480 <exit@plt>
    482e:	66 90                	xchg   %ax,%ax

0000000000004830 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    4830:	f3 0f 1e fa          	endbr64
    4834:	41 57                	push   %r15
    4836:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    4838:	4c 8d 35 46 18 00 00 	lea    0x1846(%rip),%r14        # 6085 <_IO_stdin_used+0x85>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    483f:	41 55                	push   %r13
    4841:	49 89 d5             	mov    %rdx,%r13
    4844:	41 54                	push   %r12
    4846:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    4849:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    484c:	55                   	push   %rbp
    484d:	53                   	push   %rbx
    484e:	48 83 ec 18          	sub    $0x18,%rsp
    4852:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    485b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4860:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    4862:	49 89 e7             	mov    %rsp,%r15
    4865:	4c 89 fa             	mov    %r15,%rdx
    4868:	e8 f3 da ff ff       	call   2360 <strtok_r@plt>
    for (; *str; ++str)
    486d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    4871:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    4874:	84 db                	test   %bl,%bl
    4876:	74 1d                	je     4895 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    4878:	e8 73 dc ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    487d:	48 89 ea             	mov    %rbp,%rdx
    4880:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    4883:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    4887:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    488a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    488d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4891:	84 db                	test   %bl,%bl
    4893:	75 eb                	jne    4880 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    4895:	4c 89 fa             	mov    %r15,%rdx
    4898:	4c 89 f6             	mov    %r14,%rsi
    489b:	31 ff                	xor    %edi,%edi
    489d:	e8 be da ff ff       	call   2360 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    48a2:	48 8d 35 8a 18 00 00 	lea    0x188a(%rip),%rsi        # 6133 <_IO_stdin_used+0x133>
    48a9:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    48ac:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    48af:	e8 dc da ff ff       	call   2390 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    48b4:	4c 89 ea             	mov    %r13,%rdx
    48b7:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    48ba:	85 c0                	test   %eax,%eax
    48bc:	75 2a                	jne    48e8 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    48be:	48 89 df             	mov    %rbx,%rdi
    48c1:	e8 3a fd ff ff       	call   4600 <handle_get_method>
}
    48c6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    48cb:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    48d4:	75 20                	jne    48f6 <handle_http_method+0xc6>
    48d6:	48 83 c4 18          	add    $0x18,%rsp
    48da:	5b                   	pop    %rbx
    48db:	5d                   	pop    %rbp
    48dc:	41 5c                	pop    %r12
    48de:	41 5d                	pop    %r13
    48e0:	41 5e                	pop    %r14
    48e2:	41 5f                	pop    %r15
    48e4:	c3                   	ret
    48e5:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    48e8:	48 8b 3d 29 47 00 00 	mov    0x4729(%rip),%rdi        # 9018 <unimplemented_content>
    48ef:	e8 9c fb ff ff       	call   4490 <_send_static_string_content>
}
    48f4:	eb d0                	jmp    48c6 <handle_http_method+0x96>
    48f6:	e8 15 da ff ff       	call   2310 <__stack_chk_fail@plt>
    48fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004900 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    4900:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    4904:	85 d2                	test   %edx,%edx
    4906:	7e 38                	jle    4940 <get_line+0x40>
    4908:	48 63 d2             	movslq %edx,%rdx
    490b:	48 83 c7 01          	add    $0x1,%rdi
    490f:	48 01 f2             	add    %rsi,%rdx
    4912:	eb 11                	jmp    4925 <get_line+0x25>
    4914:	0f 1f 40 00          	nopl   0x0(%rax)
    4918:	48 83 c6 01          	add    $0x1,%rsi
    491c:	48 83 c7 01          	add    $0x1,%rdi
    4920:	48 39 d6             	cmp    %rdx,%rsi
    4923:	74 1b                	je     4940 <get_line+0x40>
        dest[i] = src[i];
    4925:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4929:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    492b:	3c 0d                	cmp    $0xd,%al
    492d:	75 e9                	jne    4918 <get_line+0x18>
    492f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4932:	75 e4                	jne    4918 <get_line+0x18>
            dest[i] = '\0';
    4934:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    4937:	31 c0                	xor    %eax,%eax
    4939:	c3                   	ret
    493a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    4940:	b8 01 00 00 00       	mov    $0x1,%eax
}
    4945:	c3                   	ret
    4946:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004950 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    4950:	f3 0f 1e fa          	endbr64
    4954:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    495b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    495f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4968:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4970:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    4972:	49 89 e2             	mov    %rsp,%r10
    4975:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    497d:	4c 89 d0             	mov    %r10,%rax
    4980:	eb 13                	jmp    4995 <handle_client_request+0x45>
    4982:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4988:	48 83 c0 01          	add    $0x1,%rax
    498c:	48 83 c1 01          	add    $0x1,%rcx
    4990:	4c 39 c8             	cmp    %r9,%rax
    4993:	74 4b                	je     49e0 <handle_client_request+0x90>
        dest[i] = src[i];
    4995:	44 0f b6 01          	movzbl (%rcx),%r8d
    4999:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    499c:	41 80 f8 0d          	cmp    $0xd,%r8b
    49a0:	75 e6                	jne    4988 <handle_client_request+0x38>
    49a2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    49a6:	75 e0                	jne    4988 <handle_client_request+0x38>
            dest[i] = '\0';
    49a8:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    49ab:	8b 47 08             	mov    0x8(%rdi),%eax
    49ae:	48 89 f2             	mov    %rsi,%rdx
    49b1:	4c 89 d7             	mov    %r10,%rdi
    49b4:	89 c6                	mov    %eax,%esi
    49b6:	e8 75 fe ff ff       	call   4830 <handle_http_method>
}
    49bb:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    49c3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    49cc:	75 39                	jne    4a07 <handle_client_request+0xb7>
    49ce:	31 c0                	xor    %eax,%eax
    49d0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    49d7:	c3                   	ret
    49d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    49e0:	48 8b 0d 39 46 00 00 	mov    0x4639(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    49e7:	ba 12 00 00 00       	mov    $0x12,%edx
    49ec:	be 01 00 00 00       	mov    $0x1,%esi
    49f1:	48 8d 3d 3f 17 00 00 	lea    0x173f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    49f8:	e8 a3 da ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    49fd:	bf 01 00 00 00       	mov    $0x1,%edi
    4a02:	e8 79 da ff ff       	call   2480 <exit@plt>
}
    4a07:	e8 04 d9 ff ff       	call   2310 <__stack_chk_fail@plt>
    4a0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004a10 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    4a10:	f3 0f 1e fa          	endbr64
    4a14:	55                   	push   %rbp
    4a15:	53                   	push   %rbx
    4a16:	48 89 cb             	mov    %rcx,%rbx
    4a19:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    4a1d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4a20:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    4a23:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4a29:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    4a2c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4a2f:	f6 c1 02             	test   $0x2,%cl
    4a32:	74 00                	je     4a34 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    4a34:	41 89 c0             	mov    %eax,%r8d
    4a37:	45 29 c8             	sub    %r9d,%r8d
    4a3a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    4a3e:	0f 82 28 db ff ff    	jb     256c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    4a44:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4a47:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4a4a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    4a4d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    4a50:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    4a53:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4a57:	d3 e5                	shl    %cl,%ebp
    4a59:	48 c1 e5 06          	shl    $0x6,%rbp
    4a5d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    4a61:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    4a64:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    4a69:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    4a70:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    4a74:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    4a78:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    4a80:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    4a88:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4a8c:	e8 5f d9 ff ff       	call   23f0 <malloc@plt>
  io_uring_submit(ring);
    4a91:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    4a94:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    4a9a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    4a9e:	48 83 c4 08          	add    $0x8,%rsp
    4aa2:	5b                   	pop    %rbx
    4aa3:	5d                   	pop    %rbp
  io_uring_submit(ring);
    4aa4:	e9 77 d8 ff ff       	jmp    2320 <io_uring_submit@plt>
    4aa9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004ab0 <io_thread>:
void* io_thread(void *arg) {
    4ab0:	f3 0f 1e fa          	endbr64
    4ab4:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4ab6:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    4ab8:	41 56                	push   %r14
    4aba:	41 55                	push   %r13
    4abc:	41 54                	push   %r12
    4abe:	55                   	push   %rbp
    4abf:	48 89 fd             	mov    %rdi,%rbp
    4ac2:	53                   	push   %rbx
    4ac3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    4aca:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4ad3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4adb:	48 8b 47 40          	mov    0x40(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4adf:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4ae4:	bf 00 01 00 00       	mov    $0x100,%edi
    4ae9:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    4aec:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4af0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4af5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4afa:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4aff:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4b04:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4b0c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4b11:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4b19:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4b1e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4b26:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4b2b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4b33:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4b38:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4b40:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4b45:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4b4d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4b55:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4b5d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4b65:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4b6d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4b75:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4b7d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4b85:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4b8d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4b95:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4b9d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4ba4:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    4bac:	e8 1f d8 ff ff       	call   23d0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    4bb1:	48 8b 7d 40          	mov    0x40(%rbp),%rdi
    4bb5:	31 f6                	xor    %esi,%esi
    4bb7:	e8 04 d9 ff ff       	call   24c0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    4bbc:	31 d2                	xor    %edx,%edx
    4bbe:	be 01 00 00 00       	mov    $0x1,%esi
    4bc3:	bf 02 00 00 00       	mov    $0x2,%edi
    4bc8:	e8 43 d9 ff ff       	call   2510 <socket@plt>
  if (sock == -1)
    4bcd:	83 f8 ff             	cmp    $0xffffffff,%eax
    4bd0:	0f 84 d8 d9 ff ff    	je     25ae <io_thread.cold+0x38>
  if (setsockopt(sock,
    4bd6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4bdb:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4be1:	89 c7                	mov    %eax,%edi
    4be3:	41 89 c4             	mov    %eax,%r12d
    4be6:	ba 02 00 00 00       	mov    $0x2,%edx
    4beb:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    4bf0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    4bf8:	e8 e3 d6 ff ff       	call   22e0 <setsockopt@plt>
    4bfd:	85 c0                	test   %eax,%eax
    4bff:	0f 88 7d d9 ff ff    	js     2582 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    4c05:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    4c0a:	ba 10 00 00 00       	mov    $0x10,%edx
    4c0f:	44 89 e7             	mov    %r12d,%edi
    4c12:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4c1b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    4c23:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    4c2b:	e8 10 d8 ff ff       	call   2440 <bind@plt>
    4c30:	85 c0                	test   %eax,%eax
    4c32:	0f 88 82 d9 ff ff    	js     25ba <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    4c38:	be 0a 00 00 00       	mov    $0xa,%esi
    4c3d:	44 89 e7             	mov    %r12d,%edi
    4c40:	e8 bb d7 ff ff       	call   2400 <listen@plt>
    4c45:	85 c0                	test   %eax,%eax
    4c47:	0f 88 41 d9 ff ff    	js     258e <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4c4d:	ba db 18 00 00       	mov    $0x18db,%edx
    4c52:	48 8d 35 23 15 00 00 	lea    0x1523(%rip),%rsi        # 617c <_IO_stdin_used+0x17c>
    4c59:	bf 01 00 00 00       	mov    $0x1,%edi
    4c5e:	31 c0                	xor    %eax,%eax
    4c60:	e8 cb d7 ff ff       	call   2430 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4c65:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4c6a:	48 89 d9             	mov    %rbx,%rcx
    4c6d:	44 89 e7             	mov    %r12d,%edi
    4c70:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4c75:	48 89 c6             	mov    %rax,%rsi
    4c78:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4c7d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    4c82:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4c8a:	e8 81 fd ff ff       	call   4a10 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4c8f:	bf 01 00 00 00       	mov    $0x1,%edi
    4c94:	be 10 00 00 00       	mov    $0x10,%esi
    4c99:	e8 e2 d6 ff ff       	call   2380 <calloc@plt>
    void *buf = malloc(size);
    4c9e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    4ca3:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    4ca6:	e8 45 d7 ff ff       	call   23f0 <malloc@plt>
    if (!buf) {
    4cab:	48 85 c0             	test   %rax,%rax
    4cae:	0f 84 ae 04 00 00    	je     5162 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    4cb4:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4cb8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4cbf:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    4cc6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    4cce:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4cd1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4cd6:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4cd8:	f6 c1 02             	test   $0x2,%cl
    4cdb:	0f 85 0f 04 00 00    	jne    50f0 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    4ce1:	89 d0                	mov    %edx,%eax
    4ce3:	29 f0                	sub    %esi,%eax
    4ce5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4cec:	0f 82 b2 d8 ff ff    	jb     25a4 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    4cf2:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4cf5:	48 8d 75 48          	lea    0x48(%rbp),%rsi
	sqe->addr3 = 0;
    4cf9:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    4cfd:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d00:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4d07:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d0a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4d11:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4d18:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4d1a:	8b 55 48             	mov    0x48(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    4d1d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4d22:	48 c1 e0 06          	shl    $0x6,%rax
    4d26:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4d2e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4d34:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4d37:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4d3f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4d43:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4d4b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4d53:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4d57:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    4d5b:	e8 c0 d5 ff ff       	call   2320 <io_uring_submit@plt>
  while (data->running == 1) {
    4d60:	83 7d 2c 01          	cmpl   $0x1,0x2c(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4d64:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4d69:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4d71:	0f 85 d7 01 00 00    	jne    4f4e <io_thread+0x49e>
    4d77:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4d7c:	4d 89 ce             	mov    %r9,%r14
    4d7f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4d84:	0f 1f 40 00          	nopl   0x0(%rax)
    4d88:	48 8d 3d 03 14 00 00 	lea    0x1403(%rip),%rdi        # 6192 <_IO_stdin_used+0x192>
    4d8f:	e8 3c d5 ff ff       	call   22d0 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    4d94:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    4d9b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    4da2:	c1 e9 0b             	shr    $0xb,%ecx
    4da5:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    4da8:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4db0:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    4db2:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    4dba:	8b 16                	mov    (%rsi),%edx
		if (!available)
    4dbc:	39 d0                	cmp    %edx,%eax
    4dbe:	74 36                	je     4df6 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    4dc0:	89 f8                	mov    %edi,%eax
    4dc2:	21 d0                	and    %edx,%eax
    4dc4:	d3 e0                	shl    %cl,%eax
    4dc6:	48 c1 e0 04          	shl    $0x4,%rax
    4dca:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    4dd2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    4dda:	0f 85 a8 01 00 00    	jne    4f88 <io_thread+0x4d8>
    4de0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4de4:	0f 85 0e 03 00 00    	jne    50f8 <io_thread+0x648>
			if (cqe->res < 0)
    4dea:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4ded:	83 c2 01             	add    $0x1,%edx
    4df0:	89 16                	mov    %edx,(%rsi)
			if (!err)
    4df2:	85 c0                	test   %eax,%eax
    4df4:	79 b2                	jns    4da8 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    4df6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    4dff:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    4e00:	45 31 c0             	xor    %r8d,%r8d
    4e03:	31 d2                	xor    %edx,%edx
    4e05:	b9 01 00 00 00       	mov    $0x1,%ecx
    4e0a:	4c 89 f6             	mov    %r14,%rsi
    4e0d:	48 89 df             	mov    %rbx,%rdi
    4e10:	e8 0b d6 ff ff       	call   2420 <__io_uring_get_cqe@plt>
    4e15:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    4e18:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4e1d:	48 83 38 01          	cmpq   $0x1,(%rax)
    4e21:	0f 84 e1 02 00 00    	je     5108 <io_thread+0x658>
    4e27:	48 8d 3d 8a 13 00 00 	lea    0x138a(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4e2e:	e8 9d d4 ff ff       	call   22d0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4e33:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4e38:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    4e3b:	45 85 ff             	test   %r15d,%r15d
    4e3e:	0f 88 32 d7 ff ff    	js     2576 <io_thread.cold>
      if (cqe->res < 0) {
    4e44:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    4e47:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    4e4b:	85 c0                	test   %eax,%eax
    4e4d:	0f 88 d5 02 00 00    	js     5128 <io_thread+0x678>
      switch (req->event_type) {
    4e53:	41 83 f8 01          	cmp    $0x1,%r8d
    4e57:	0f 84 7b 01 00 00    	je     4fd8 <io_thread+0x528>
    4e5d:	41 83 f8 02          	cmp    $0x2,%r8d
    4e61:	0f 84 a1 01 00 00    	je     5008 <io_thread+0x558>
    4e67:	45 85 c0             	test   %r8d,%r8d
    4e6a:	0f 85 50 01 00 00    	jne    4fc0 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    4e70:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    4e75:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    4e7a:	48 89 d9             	mov    %rbx,%rcx
    4e7d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    4e81:	e8 8a fb ff ff       	call   4a10 <add_accept_request>
              add_read_request(cqe->res, &ring);
    4e86:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4e8b:	48 89 de             	mov    %rbx,%rsi
    4e8e:	8b 78 08             	mov    0x8(%rax),%edi
    4e91:	e8 1a f5 ff ff       	call   43b0 <add_read_request>
              free(req);
    4e96:	4c 89 e7             	mov    %r12,%rdi
    4e99:	e8 12 d4 ff ff       	call   22b0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    4e9e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    4ea3:	48 85 c0             	test   %rax,%rax
    4ea6:	0f 85 14 01 00 00    	jne    4fc0 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    4eac:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4eb3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    4eba:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    4ebd:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4ec2:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    4ec4:	f6 c1 02             	test   $0x2,%cl
    4ec7:	74 00                	je     4ec9 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    4ec9:	89 d0                	mov    %edx,%eax
    4ecb:	29 f0                	sub    %esi,%eax
    4ecd:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4ed4:	0f 82 c0 d6 ff ff    	jb     259a <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    4eda:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    4edd:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    4ee2:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    4ee6:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ee9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    4ef0:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4ef3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    4efa:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    4f01:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    4f03:	8b 55 48             	mov    0x48(%rbp),%edx
    4f06:	48 c1 e0 06          	shl    $0x6,%rax
    4f0a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    4f12:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    4f18:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    4f1b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    4f23:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    4f27:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    4f2f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    4f37:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    4f3b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    4f3f:	e8 dc d3 ff ff       	call   2320 <io_uring_submit@plt>
  while (data->running == 1) {
    4f44:	83 7d 2c 01          	cmpl   $0x1,0x2c(%rbp)
    4f48:	0f 84 3a fe ff ff    	je     4d88 <io_thread+0x2d8>
    4f4e:	48 8d 3d 9c 12 00 00 	lea    0x129c(%rip),%rdi        # 61f1 <_IO_stdin_used+0x1f1>
    4f55:	e8 76 d3 ff ff       	call   22d0 <puts@plt>
}
    4f5a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    4f62:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4f6b:	0f 85 18 02 00 00    	jne    5189 <io_thread+0x6d9>
    4f71:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    4f78:	31 c0                	xor    %eax,%eax
    4f7a:	5b                   	pop    %rbx
    4f7b:	5d                   	pop    %rbp
    4f7c:	41 5c                	pop    %r12
    4f7e:	41 5d                	pop    %r13
    4f80:	41 5e                	pop    %r14
    4f82:	41 5f                	pop    %r15
    4f84:	c3                   	ret
    4f85:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    4f88:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    4f8d:	48 85 c0             	test   %rax,%rax
    4f90:	0f 84 6a fe ff ff    	je     4e00 <io_thread+0x350>
      if (cqe->user_data == 1) {
    4f96:	48 83 38 01          	cmpq   $0x1,(%rax)
    4f9a:	0f 84 68 01 00 00    	je     5108 <io_thread+0x658>
    4fa0:	48 8d 3d 11 12 00 00 	lea    0x1211(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4fa7:	e8 24 d3 ff ff       	call   22d0 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    4fac:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4fb1:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    4fb4:	e9 8b fe ff ff       	jmp    4e44 <io_thread+0x394>
    4fb9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    4fc0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    4fc8:	8b 02                	mov    (%rdx),%eax
    4fca:	83 c0 01             	add    $0x1,%eax
    4fcd:	89 02                	mov    %eax,(%rdx)
}
    4fcf:	e9 d8 fe ff ff       	jmp    4eac <io_thread+0x3fc>
    4fd4:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    4fd8:	85 c0                	test   %eax,%eax
    4fda:	75 74                	jne    5050 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4fdc:	48 8b 0d 3d 40 00 00 	mov    0x403d(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4fe3:	ba 0f 00 00 00       	mov    $0xf,%edx
    4fe8:	be 01 00 00 00       	mov    $0x1,%esi
    4fed:	48 8d 3d ed 11 00 00 	lea    0x11ed(%rip),%rdi        # 61e1 <_IO_stdin_used+0x1e1>
    4ff4:	e8 a7 d4 ff ff       	call   24a0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    4ff9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4ffe:	e9 a0 fe ff ff       	jmp    4ea3 <io_thread+0x3f3>
    5003:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5008:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    500d:	45 31 ff             	xor    %r15d,%r15d
    5010:	85 c0                	test   %eax,%eax
    5012:	7e 20                	jle    5034 <io_thread+0x584>
    5014:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5018:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    501b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    501f:	48 c1 e0 04          	shl    $0x4,%rax
    5023:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5028:	e8 83 d2 ff ff       	call   22b0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    502d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5032:	7f e4                	jg     5018 <io_thread+0x568>
              close(req->client_socket);
    5034:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5039:	e8 12 d3 ff ff       	call   2350 <close@plt>
              free(req);
    503e:	4c 89 e7             	mov    %r12,%rdi
    5041:	e8 6a d2 ff ff       	call   22b0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5046:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    504b:	e9 53 fe ff ff       	jmp    4ea3 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5050:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5055:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    505a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5062:	eb 11                	jmp    5075 <io_thread+0x5c5>
    5064:	0f 1f 40 00          	nopl   0x0(%rax)
    5068:	48 83 c0 01          	add    $0x1,%rax
    506c:	48 83 c2 01          	add    $0x1,%rdx
    5070:	48 39 c6             	cmp    %rax,%rsi
    5073:	74 4b                	je     50c0 <io_thread+0x610>
        dest[i] = src[i];
    5075:	0f b6 0a             	movzbl (%rdx),%ecx
    5078:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    507a:	80 f9 0d             	cmp    $0xd,%cl
    507d:	75 e9                	jne    5068 <io_thread+0x5b8>
    507f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5083:	75 e3                	jne    5068 <io_thread+0x5b8>
            dest[i] = '\0';
    5085:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5088:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    508d:	48 89 da             	mov    %rbx,%rdx
    5090:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5095:	e8 96 f7 ff ff       	call   4830 <handle_http_method>
              free(req->iov[0].iov_base);
    509a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    509f:	e8 0c d2 ff ff       	call   22b0 <free@plt>
              free(req);
    50a4:	4c 89 e7             	mov    %r12,%rdi
    50a7:	e8 04 d2 ff ff       	call   22b0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    50ac:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    50b1:	e9 ed fd ff ff       	jmp    4ea3 <io_thread+0x3f3>
    50b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    50c0:	48 8b 0d 59 3f 00 00 	mov    0x3f59(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    50c7:	ba 12 00 00 00       	mov    $0x12,%edx
    50cc:	be 01 00 00 00       	mov    $0x1,%esi
    50d1:	48 8d 3d 5f 10 00 00 	lea    0x105f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    50d8:	e8 c3 d3 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    50dd:	bf 01 00 00 00       	mov    $0x1,%edi
    50e2:	e8 99 d3 ff ff       	call   2480 <exit@plt>
    50e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    50f0:	e9 ec fb ff ff       	jmp    4ce1 <io_thread+0x231>
    50f5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    50f8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    50fd:	e9 94 fe ff ff       	jmp    4f96 <io_thread+0x4e6>
    5102:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5108:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5110:	48 8d 3d 8d 10 00 00 	lea    0x108d(%rip),%rdi        # 61a4 <_IO_stdin_used+0x1a4>
    5117:	8b 02                	mov    (%rdx),%eax
    5119:	83 c0 01             	add    $0x1,%eax
    511c:	89 02                	mov    %eax,(%rdx)
    511e:	e8 ad d1 ff ff       	call   22d0 <puts@plt>
    5123:	e9 26 fe ff ff       	jmp    4f4e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5128:	f7 d8                	neg    %eax
    512a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    512f:	89 c7                	mov    %eax,%edi
    5131:	e8 aa d3 ff ff       	call   24e0 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5136:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    513b:	be 01 00 00 00       	mov    $0x1,%esi
    5140:	48 8b 3d d9 3e 00 00 	mov    0x3ed9(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    5147:	48 89 c1             	mov    %rax,%rcx
    514a:	48 8d 15 ff 12 00 00 	lea    0x12ff(%rip),%rdx        # 6450 <_IO_stdin_used+0x450>
    5151:	31 c0                	xor    %eax,%eax
    5153:	e8 58 d3 ff ff       	call   24b0 <__fprintf_chk@plt>
          exit(1);
    5158:	bf 01 00 00 00       	mov    $0x1,%edi
    515d:	e8 1e d3 ff ff       	call   2480 <exit@plt>
    5162:	48 8b 0d b7 3e 00 00 	mov    0x3eb7(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    5169:	ba 28 00 00 00       	mov    $0x28,%edx
    516e:	be 01 00 00 00       	mov    $0x1,%esi
    5173:	48 8d 3d a6 12 00 00 	lea    0x12a6(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    517a:	e8 21 d3 ff ff       	call   24a0 <fwrite@plt>
        exit(1);
    517f:	bf 01 00 00 00       	mov    $0x1,%edi
    5184:	e8 f7 d2 ff ff       	call   2480 <exit@plt>
}
    5189:	e8 82 d1 ff ff       	call   2310 <__stack_chk_fail@plt>
    518e:	66 90                	xchg   %ax,%ax

0000000000005190 <receive>:
int receive(struct BarrierTask *data) {
    5190:	f3 0f 1e fa          	endbr64
  for (int n = 0 ; n < data->thread_count; n++) {
    5194:	8b 87 24 02 00 00    	mov    0x224(%rdi),%eax
    519a:	85 c0                	test   %eax,%eax
    519c:	0f 8e f8 00 00 00    	jle    529a <receive+0x10a>
int receive(struct BarrierTask *data) {
    51a2:	41 54                	push   %r12
    51a4:	4c 63 e0             	movslq %eax,%r12
    51a7:	48 89 fa             	mov    %rdi,%rdx
    51aa:	55                   	push   %rbp
    51ab:	49 c1 e4 09          	shl    $0x9,%r12
    51af:	53                   	push   %rbx
    51b0:	48 8b b7 88 04 00 00 	mov    0x488(%rdi),%rsi
    51b7:	49 01 f4             	add    %rsi,%r12
    51ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    51c0:	48 8b 2e             	mov    (%rsi),%rbp
    for (int x = 0 ; x < me->messages_count ; x++) {
    51c3:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    51ca:	48 85 ff             	test   %rdi,%rdi
    51cd:	0f 8e a5 00 00 00    	jle    5278 <receive+0xe8>
      data->sends++;
    51d3:	48 8b 8a 00 05 00 00 	mov    0x500(%rdx),%rcx
    51da:	4c 8b 45 00          	mov    0x0(%rbp),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    51de:	4c 63 1a             	movslq (%rdx),%r11
    51e1:	49 89 c9             	mov    %rcx,%r9
    51e4:	48 8d 41 01          	lea    0x1(%rcx),%rax
    51e8:	49 f7 d9             	neg    %r9
    51eb:	48 01 c7             	add    %rax,%rdi
    51ee:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    51f2:	4c 8b 8a 80 01 00 00 	mov    0x180(%rdx),%r9
      data->mailboxes[n].received++;
    51f9:	4c 8b 86 80 01 00 00 	mov    0x180(%rsi),%r8
      data->n++;
    5200:	49 29 c9             	sub    %rcx,%r9
      data->mailboxes[n].received++;
    5203:	49 29 c8             	sub    %rcx,%r8
    5206:	eb 11                	jmp    5219 <receive+0x89>
    5208:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < me->messages_count ; x++) {
    5210:	48 83 c0 01          	add    $0x1,%rax
    5214:	48 39 c7             	cmp    %rax,%rdi
    5217:	74 5f                	je     5278 <receive+0xe8>
      data->n++;
    5219:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
      data->sends++;
    521d:	48 89 82 00 05 00 00 	mov    %rax,0x500(%rdx)
      data->n++;
    5224:	48 89 8a 80 01 00 00 	mov    %rcx,0x180(%rdx)
      data->mailboxes[n].received++;
    522b:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    522f:	48 89 8e 80 01 00 00 	mov    %rcx,0x180(%rsi)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    5236:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    523b:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    523f:	75 cf                	jne    5210 <receive+0x80>
    5241:	48 63 9a 20 02 00 00 	movslq 0x220(%rdx),%rbx
    5248:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    524c:	75 c2                	jne    5210 <receive+0x80>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    524e:	bf 01 00 00 00       	mov    $0x1,%edi
    5253:	b9 01 00 00 00       	mov    $0x1,%ecx
    5258:	ba 01 00 00 00       	mov    $0x1,%edx
    525d:	31 c0                	xor    %eax,%eax
    525f:	48 8d 35 12 12 00 00 	lea    0x1212(%rip),%rsi        # 6478 <_IO_stdin_used+0x478>
    5266:	e8 c5 d1 ff ff       	call   2430 <__printf_chk@plt>
        exit(1);
    526b:	bf 01 00 00 00       	mov    $0x1,%edi
    5270:	e8 0b d2 ff ff       	call   2480 <exit@plt>
    5275:	0f 1f 00             	nopl   (%rax)
  for (int n = 0 ; n < data->thread_count; n++) {
    5278:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
    me->messages_count = 0;
    527f:	48 c7 85 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rbp)
  for (int n = 0 ; n < data->thread_count; n++) {
    528a:	49 39 f4             	cmp    %rsi,%r12
    528d:	0f 85 2d ff ff ff    	jne    51c0 <receive+0x30>
}
    5293:	5b                   	pop    %rbx
    5294:	31 c0                	xor    %eax,%eax
    5296:	5d                   	pop    %rbp
    5297:	41 5c                	pop    %r12
    5299:	c3                   	ret
    529a:	31 c0                	xor    %eax,%eax
    529c:	c3                   	ret
    529d:	0f 1f 00             	nopl   (%rax)

00000000000052a0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    52a0:	f3 0f 1e fa          	endbr64
    52a4:	41 57                	push   %r15
    52a6:	41 56                	push   %r14
    52a8:	41 55                	push   %r13
    52aa:	41 54                	push   %r12
    52ac:	55                   	push   %rbp
    52ad:	53                   	push   %rbx
    52ae:	48 89 fb             	mov    %rdi,%rbx
    52b1:	48 83 ec 28          	sub    $0x28,%rsp
  if (data->thread_index == data->task_index) {
    52b5:	8b 07                	mov    (%rdi),%eax
    52b7:	39 87 20 02 00 00    	cmp    %eax,0x220(%rdi)
    52bd:	0f 84 65 01 00 00    	je     5428 <barriered_work+0x188>
    receive(data);
    52c3:	e8 c8 fe ff ff       	call   5190 <receive>
    while (data->scheduled == 1) {
    52c8:	83 bb 00 03 00 00 01 	cmpl   $0x1,0x300(%rbx)
    52cf:	75 1b                	jne    52ec <barriered_work+0x4c>
    52d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    52d8:	48 83 83 80 01 00 00 01 	addq   $0x1,0x180(%rbx)
      asm volatile ("sfence" ::: "memory");
    52e0:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    52e3:	83 bb 00 03 00 00 01 	cmpl   $0x1,0x300(%rbx)
    52ea:	74 ec                	je     52d8 <barriered_work+0x38>
    if (data->sending == 1) {
    52ec:	83 bb 08 05 00 00 01 	cmpl   $0x1,0x508(%rbx)
    52f3:	74 14                	je     5309 <barriered_work+0x69>
  asm volatile ("mfence" ::: "memory");
    52f5:	0f ae f0             	mfence
}
    52f8:	48 83 c4 28          	add    $0x28,%rsp
    52fc:	31 c0                	xor    %eax,%eax
    52fe:	5b                   	pop    %rbx
    52ff:	5d                   	pop    %rbp
    5300:	41 5c                	pop    %r12
    5302:	41 5d                	pop    %r13
    5304:	41 5e                	pop    %r14
    5306:	41 5f                	pop    %r15
    5308:	c3                   	ret
        for (int n = 0 ; n < data->thread_count; n++) {
    5309:	8b 83 24 02 00 00    	mov    0x224(%rbx),%eax
    530f:	85 c0                	test   %eax,%eax
    5311:	7e e2                	jle    52f5 <barriered_work+0x55>
          if (n == data->thread_index) { continue; }
    5313:	8b bb 20 02 00 00    	mov    0x220(%rbx),%edi
    5319:	4c 63 f8             	movslq %eax,%r15
    531c:	48 8d 83 10 05 00 00 	lea    0x510(%rbx),%rax
    5323:	31 d2                	xor    %edx,%edx
    5325:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    532a:	48 8d 83 18 05 00 00 	lea    0x518(%rbx),%rax
    5331:	89 7c 24 04          	mov    %edi,0x4(%rsp)
    5335:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    533a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5340:	39 54 24 04          	cmp    %edx,0x4(%rsp)
    5344:	0f 84 c7 00 00 00    	je     5411 <barriered_work+0x171>
          struct Data *them = data->mailboxes[n].higher;
    534a:	49 89 d0             	mov    %rdx,%r8
    534d:	49 c1 e0 09          	shl    $0x9,%r8
    5351:	4c 03 83 88 04 00 00 	add    0x488(%rbx),%r8
    5358:	4d 8b 88 80 00 00 00 	mov    0x80(%r8),%r9
          for (; them->messages_count < min;) {
    535f:	4d 8b 99 80 00 00 00 	mov    0x80(%r9),%r11
    5366:	49 63 b9 88 00 00 00 	movslq 0x88(%r9),%rdi
    536d:	49 39 fb             	cmp    %rdi,%r11
    5370:	0f 8d 9b 00 00 00    	jge    5411 <barriered_work+0x171>
    5376:	49 89 fa             	mov    %rdi,%r10
    5379:	4c 8b b3 80 01 00 00 	mov    0x180(%rbx),%r14
    5380:	49 8b a8 00 01 00 00 	mov    0x100(%r8),%rbp
    5387:	4d 29 da             	sub    %r11,%r10
            them->messages[them->messages_count++] = data->message; 
    538a:	49 8b 09             	mov    (%r9),%rcx
    538d:	49 8d 42 ff          	lea    -0x1(%r10),%rax
    5391:	48 83 f8 02          	cmp    $0x2,%rax
    5395:	0f 86 a5 02 00 00    	jbe    5640 <barriered_work+0x3a0>
    539b:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    53a3:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    53ab:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    53af:	4c 8d 2c 31          	lea    (%rcx,%rsi,1),%r13
    53b3:	4c 39 6c 24 08       	cmp    %r13,0x8(%rsp)
    53b8:	0f 83 0a 02 00 00    	jae    55c8 <barriered_work+0x328>
    53be:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    53c3:	4d 39 ec             	cmp    %r13,%r12
    53c6:	0f 83 fc 01 00 00    	jae    55c8 <barriered_work+0x328>
    53cc:	4c 8d 1c 01          	lea    (%rcx,%rax,1),%r11
    53d0:	48 01 ce             	add    %rcx,%rsi
    53d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    53d8:	48 8b 83 10 05 00 00 	mov    0x510(%rbx),%rax
          for (; them->messages_count < min;) {
    53df:	49 83 c3 08          	add    $0x8,%r11
            them->messages[them->messages_count++] = data->message; 
    53e3:	49 89 43 f8          	mov    %rax,-0x8(%r11)
          for (; them->messages_count < min;) {
    53e7:	4c 39 de             	cmp    %r11,%rsi
    53ea:	75 ec                	jne    53d8 <barriered_work+0x138>
    53ec:	0f 1f 40 00          	nopl   0x0(%rax)
    53f0:	4b 8d 34 16          	lea    (%r14,%r10,1),%rsi
    53f4:	4c 01 d5             	add    %r10,%rbp
    53f7:	48 89 b3 80 01 00 00 	mov    %rsi,0x180(%rbx)
    53fe:	49 89 a8 00 01 00 00 	mov    %rbp,0x100(%r8)
    5405:	49 89 b9 80 00 00 00 	mov    %rdi,0x80(%r9)
    540c:	48 89 44 f9 f8       	mov    %rax,-0x8(%rcx,%rdi,8)
        for (int n = 0 ; n < data->thread_count; n++) {
    5411:	48 83 c2 01          	add    $0x1,%rdx
    5415:	4c 39 fa             	cmp    %r15,%rdx
    5418:	0f 85 22 ff ff ff    	jne    5340 <barriered_work+0xa0>
    541e:	e9 d2 fe ff ff       	jmp    52f5 <barriered_work+0x55>
    5423:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      receive(data);
    5428:	e8 63 fd ff ff       	call   5190 <receive>
        for (int y = 0; y < data->thread_count ; y++) {
    542d:	8b 8b 24 02 00 00    	mov    0x224(%rbx),%ecx
        int t = data->task_index;
    5433:	8b 03                	mov    (%rbx),%eax
        for (int y = 0; y < data->thread_count ; y++) {
    5435:	85 c9                	test   %ecx,%ecx
    5437:	0f 8e 9e 00 00 00    	jle    54db <barriered_work+0x23b>
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    543d:	48 63 d0             	movslq %eax,%rdx
              int next_task = abs((t + 1) % (data->thread_count));
    5440:	83 c0 01             	add    $0x1,%eax
    5443:	4c 63 d9             	movslq %ecx,%r11
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    5446:	48 8d 34 92          	lea    (%rdx,%rdx,4),%rsi
    544a:	48 8d 2c 72          	lea    (%rdx,%rsi,2),%rbp
              int next_task = abs((t + 1) % (data->thread_count));
    544e:	99                   	cltd
    544f:	f7 f9                	idiv   %ecx
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    5451:	48 c1 e5 07          	shl    $0x7,%rbp
              int next_task = abs((t + 1) % (data->thread_count));
    5455:	89 d0                	mov    %edx,%eax
    5457:	f7 d8                	neg    %eax
    5459:	0f 48 c2             	cmovs  %edx,%eax
    545c:	49 c1 e3 09          	shl    $0x9,%r11
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5460:	31 ff                	xor    %edi,%edi
    5462:	48 98                	cltq
    5464:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    5468:	4c 8d 0c 50          	lea    (%rax,%rdx,2),%r9
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    546c:	48 8b 83 18 02 00 00 	mov    0x218(%rbx),%rax
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    5473:	49 c1 e1 07          	shl    $0x7,%r9
    5477:	4c 8b 60 10          	mov    0x10(%rax),%r12
    547b:	49 83 c4 20          	add    $0x20,%r12
    547f:	4d 89 e2             	mov    %r12,%r10
    5482:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    5488:	49 8b 02             	mov    (%r10),%rax
    548b:	4c 89 e2             	mov    %r12,%rdx
    548e:	48 8b 84 28 88 04 00 00 	mov    0x488(%rax,%rbp,1),%rax
    5496:	4d 8d 04 03          	lea    (%r11,%rax,1),%r8
    549a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    54a0:	48 8b 0a             	mov    (%rdx),%rcx
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
    54a3:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
          for (int b = 0; b < data->thread_count ; b++) {
    54aa:	48 05 00 02 00 00    	add    $0x200,%rax
    54b0:	48 81 c2 00 03 00 00 	add    $0x300,%rdx
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    54b7:	4a 8b 8c 09 88 04 00 00 	mov    0x488(%rcx,%r9,1),%rcx
    54bf:	48 89 34 39          	mov    %rsi,(%rcx,%rdi,1)
          for (int b = 0; b < data->thread_count ; b++) {
    54c3:	49 39 c0             	cmp    %rax,%r8
    54c6:	75 d8                	jne    54a0 <barriered_work+0x200>
        for (int y = 0; y < data->thread_count ; y++) {
    54c8:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    54cf:	49 81 c2 00 03 00 00 	add    $0x300,%r10
    54d6:	4c 39 df             	cmp    %r11,%rdi
    54d9:	75 ad                	jne    5488 <barriered_work+0x1e8>
      asm volatile ("mfence" ::: "memory");
    54db:	0f ae f0             	mfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    54de:	48 8b b3 00 04 00 00 	mov    0x400(%rbx),%rsi
    54e5:	31 ff                	xor    %edi,%edi
    54e7:	48 c1 e6 08          	shl    $0x8,%rsi
    54eb:	48 03 b3 08 03 00 00 	add    0x308(%rbx),%rsi
    54f2:	e8 f9 cd ff ff       	call   22f0 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    54f7:	48 8b 93 18 02 00 00 	mov    0x218(%rbx),%rdx
    while (data->scheduled == 1) {
    54fe:	83 bb 00 03 00 00 01 	cmpl   $0x1,0x300(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    5505:	48 8b 42 30          	mov    0x30(%rdx),%rax
    5509:	8b b8 00 01 00 00    	mov    0x100(%rax),%edi
    550f:	8d 6f 01             	lea    0x1(%rdi),%ebp
    5512:	89 a8 00 01 00 00    	mov    %ebp,0x100(%rax)
    while (data->scheduled == 1) {
    5518:	74 0d                	je     5527 <barriered_work+0x287>
    551a:	eb 6a                	jmp    5586 <barriered_work+0x2e6>
    551c:	0f 1f 40 00          	nopl   0x0(%rax)
    if (modcount != data->thread->protected_state->modcount) {
    5520:	48 8b 93 18 02 00 00 	mov    0x218(%rbx),%rdx
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
    5527:	48 63 83 20 02 00 00 	movslq 0x220(%rbx),%rax
      data->n++;
    552e:	48 83 83 80 01 00 00 01 	addq   $0x1,0x180(%rbx)
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
    5536:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    553a:	48 c1 e0 08          	shl    $0x8,%rax
    553e:	48 03 42 10          	add    0x10(%rdx),%rax
    5542:	48 63 13             	movslq (%rbx),%rdx
    5545:	48 8d 0c 92          	lea    (%rdx,%rdx,4),%rcx
    5549:	48 8d 3c 4a          	lea    (%rdx,%rcx,2),%rdi
    554d:	48 c1 e7 07          	shl    $0x7,%rdi
    5551:	48 03 78 20          	add    0x20(%rax),%rdi
    5555:	ff 93 10 02 00 00    	call   *0x210(%rbx)
      asm volatile ("sfence" ::: "memory");
    555b:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    555e:	83 bb 00 03 00 00 01 	cmpl   $0x1,0x300(%rbx)
    5565:	74 b9                	je     5520 <barriered_work+0x280>
    if (modcount != data->thread->protected_state->modcount) {
    5567:	48 8b 83 18 02 00 00 	mov    0x218(%rbx),%rax
    556e:	48 8b 40 30          	mov    0x30(%rax),%rax
    5572:	3b a8 00 01 00 00    	cmp    0x100(%rax),%ebp
    5578:	74 0c                	je     5586 <barriered_work+0x2e6>
    557a:	48 8d 3d 83 0c 00 00 	lea    0xc83(%rip),%rdi        # 6204 <_IO_stdin_used+0x204>
    5581:	e8 4a cd ff ff       	call   22d0 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    5586:	48 8b b3 00 04 00 00 	mov    0x400(%rbx),%rsi
    558d:	31 ff                	xor    %edi,%edi
    558f:	48 c1 e6 08          	shl    $0x8,%rsi
    5593:	48 03 b3 08 03 00 00 	add    0x308(%rbx),%rsi
    559a:	48 83 ee 80          	sub    $0xffffffffffffff80,%rsi
    559e:	e8 4d cd ff ff       	call   22f0 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    55a3:	48 8b 83 00 04 00 00 	mov    0x400(%rbx),%rax
    55aa:	48 83 c0 01          	add    $0x1,%rax
    55ae:	48 99                	cqto
    55b0:	48 f7 bb 80 03 00 00 	idivq  0x380(%rbx)
    55b7:	48 89 93 00 04 00 00 	mov    %rdx,0x400(%rbx)
    55be:	e9 32 fd ff ff       	jmp    52f5 <barriered_work+0x55>
    55c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    55c8:	48 8b 83 10 05 00 00 	mov    0x510(%rbx),%rax
    55cf:	4d 89 d5             	mov    %r10,%r13
    55d2:	4c 89 e6             	mov    %r12,%rsi
    55d5:	49 d1 ed             	shr    %r13
    55d8:	49 c1 e5 04          	shl    $0x4,%r13
    55dc:	66 48 0f 6e c0       	movq   %rax,%xmm0
    55e1:	4c 89 6c 24 18       	mov    %r13,0x18(%rsp)
    55e6:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    55ea:	4d 01 e5             	add    %r12,%r13
    55ed:	f6 44 24 18 10       	testb  $0x10,0x18(%rsp)
    55f2:	74 14                	je     5608 <barriered_work+0x368>
            them->messages[them->messages_count++] = data->message; 
    55f4:	48 83 c6 10          	add    $0x10,%rsi
    55f8:	41 0f 11 04 24       	movups %xmm0,(%r12)
          for (; them->messages_count < min;) {
    55fd:	49 39 f5             	cmp    %rsi,%r13
    5600:	74 16                	je     5618 <barriered_work+0x378>
    5602:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
    5608:	0f 11 06             	movups %xmm0,(%rsi)
    560b:	48 83 c6 20          	add    $0x20,%rsi
    560f:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
          for (; them->messages_count < min;) {
    5613:	49 39 f5             	cmp    %rsi,%r13
    5616:	75 f0                	jne    5608 <barriered_work+0x368>
    5618:	4c 89 d6             	mov    %r10,%rsi
    561b:	48 83 e6 fe          	and    $0xfffffffffffffffe,%rsi
    561f:	4c 01 de             	add    %r11,%rsi
    5622:	41 f6 c2 01          	test   $0x1,%r10b
    5626:	0f 84 c4 fd ff ff    	je     53f0 <barriered_work+0x150>
            them->messages[them->messages_count++] = data->message; 
    562c:	48 8b 83 10 05 00 00 	mov    0x510(%rbx),%rax
    5633:	48 89 04 f1          	mov    %rax,(%rcx,%rsi,8)
          for (; them->messages_count < min;) {
    5637:	e9 b4 fd ff ff       	jmp    53f0 <barriered_work+0x150>
    563c:	0f 1f 40 00          	nopl   0x0(%rax)
    5640:	4a 8d 04 dd 00 00 00 00 	lea    0x0(,%r11,8),%rax
    5648:	48 8d 34 fd 00 00 00 00 	lea    0x0(,%rdi,8),%rsi
    5650:	e9 77 fd ff ff       	jmp    53cc <barriered_work+0x12c>
    5655:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005660 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5660:	f3 0f 1e fa          	endbr64
    5664:	48 83 ec 08          	sub    $0x8,%rsp
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    5668:	48 8b 87 18 02 00 00 	mov    0x218(%rdi),%rax
    566f:	48 8b 40 38          	mov    0x38(%rax),%rax
    5673:	48 63 10             	movslq (%rax),%rdx
    5676:	85 d2                	test   %edx,%edx
    5678:	7e 34                	jle    56ae <barriered_work_ingest+0x4e>
    567a:	48 8b 40 08          	mov    0x8(%rax),%rax
    567e:	48 c1 e2 08          	shl    $0x8,%rdx
    5682:	48 01 c2             	add    %rax,%rdx
    5685:	0f 1f 00             	nopl   (%rax)
    if (data->thread->buffers->buffer[x].available == 1) {
    5688:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    568f:	75 12                	jne    56a3 <barriered_work_ingest+0x43>
      data->ingest_count++;
    5691:	48 83 87 80 04 00 00 01 	addq   $0x1,0x480(%rdi)
      data->thread->buffers->buffer[x].available = 0;
    5699:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    56a3:	48 05 00 01 00 00    	add    $0x100,%rax
    56a9:	48 39 d0             	cmp    %rdx,%rax
    56ac:	75 da                	jne    5688 <barriered_work_ingest+0x28>
  asm volatile ("mfence" ::: "memory");
    56ae:	0f ae f0             	mfence
  barriered_work(data);
    56b1:	e8 ea fb ff ff       	call   52a0 <barriered_work>
}
    56b6:	31 c0                	xor    %eax,%eax
    56b8:	48 83 c4 08          	add    $0x8,%rsp
    56bc:	c3                   	ret
    56bd:	0f 1f 00             	nopl   (%rax)

00000000000056c0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    56c0:	f3 0f 1e fa          	endbr64
}
    56c4:	31 c0                	xor    %eax,%eax
    56c6:	c3                   	ret
    56c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000056d0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    56d0:	f3 0f 1e fa          	endbr64
    56d4:	31 c0                	xor    %eax,%eax
    56d6:	c3                   	ret
    56d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000056e0 <after>:
int after(struct timespec left, struct timespec right) {
    56e0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    56e4:	31 c0                	xor    %eax,%eax
    56e6:	48 39 d7             	cmp    %rdx,%rdi
    56e9:	7e 08                	jle    56f3 <after+0x13>
    56eb:	31 c0                	xor    %eax,%eax
    56ed:	48 39 ce             	cmp    %rcx,%rsi
    56f0:	0f 9f c0             	setg   %al
}
    56f3:	c3                   	ret
    56f4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    56ff:	90                   	nop

0000000000005700 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    5700:	f3 0f 1e fa          	endbr64
    5704:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5709:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    570e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5710:	48 39 d7             	cmp    %rdx,%rdi
    5713:	7f 18                	jg     572d <within+0x2d>
    5715:	4d 39 d8             	cmp    %r11,%r8
    5718:	0f 9e c2             	setle  %dl
    571b:	48 39 ce             	cmp    %rcx,%rsi
    571e:	0f 9e c0             	setle  %al
    5721:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5723:	31 c0                	xor    %eax,%eax
    5725:	4d 39 d1             	cmp    %r10,%r9
    5728:	0f 9e c0             	setle  %al
    572b:	21 d0                	and    %edx,%eax
}
    572d:	c3                   	ret
    572e:	66 90                	xchg   %ax,%ax

0000000000005730 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    5730:	f3 0f 1e fa          	endbr64
    5734:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5739:	48 8b b4 24 08 01 00 00 	mov    0x108(%rsp),%rsi
    5741:	4c 8b 8c 24 88 00 00 00 	mov    0x88(%rsp),%r9
    5749:	4c 8b 94 24 90 00 00 00 	mov    0x90(%rsp),%r10
    5751:	4c 8b 84 24 88 01 00 00 	mov    0x188(%rsp),%r8
    5759:	4c 8b 9c 24 90 01 00 00 	mov    0x190(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    5761:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5766:	48 8b 94 24 10 01 00 00 	mov    0x110(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    576e:	48 39 fe             	cmp    %rdi,%rsi
    5771:	7d 2d                	jge    57a0 <overlap+0x70>
    5773:	48 39 ca             	cmp    %rcx,%rdx
    5776:	7d 60                	jge    57d8 <overlap+0xa8>
    5778:	4d 39 da             	cmp    %r11,%r10
    577b:	7d 0e                	jge    578b <overlap+0x5b>
    return 1;
    577d:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    5782:	4d 39 c1             	cmp    %r8,%r9
    5785:	0f 8c 7d 00 00 00    	jl     5808 <overlap+0xd8>
  return 0;
    578b:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    578d:	4d 39 c1             	cmp    %r8,%r9
    5790:	7f 4a                	jg     57dc <overlap+0xac>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5792:	31 c0                	xor    %eax,%eax
    5794:	4d 39 da             	cmp    %r11,%r10
    5797:	0f 9e c0             	setle  %al
    579a:	c3                   	ret
    579b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    57a0:	7e 4e                	jle    57f0 <overlap+0xc0>
    57a2:	48 39 ca             	cmp    %rcx,%rdx
    57a5:	7f 39                	jg     57e0 <overlap+0xb0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    57a7:	75 31                	jne    57da <overlap+0xaa>
    57a9:	4d 39 c1             	cmp    %r8,%r9
    57ac:	7c 2c                	jl     57da <overlap+0xaa>
    return 1;
    57ae:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    57b3:	4d 39 da             	cmp    %r11,%r10
    57b6:	7d 24                	jge    57dc <overlap+0xac>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    57b8:	48 39 ca             	cmp    %rcx,%rdx
    57bb:	0f 94 c2             	sete   %dl
    57be:	48 39 fe             	cmp    %rdi,%rsi
    57c1:	0f 94 c0             	sete   %al
    57c4:	21 c2                	and    %eax,%edx
    57c6:	31 c0                	xor    %eax,%eax
    57c8:	4d 39 c1             	cmp    %r8,%r9
    57cb:	0f 94 c0             	sete   %al
    57ce:	21 d0                	and    %edx,%eax
    57d0:	c3                   	ret
    57d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    57d8:	74 b1                	je     578b <overlap+0x5b>
  return 0;
    57da:	31 c0                	xor    %eax,%eax
}
    57dc:	c3                   	ret
    57dd:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    57e0:	4d 39 da             	cmp    %r11,%r10
    57e3:	7e c4                	jle    57a9 <overlap+0x79>
    return 1;
    57e5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    57ea:	4d 39 c1             	cmp    %r8,%r9
    57ed:	7e ba                	jle    57a9 <overlap+0x79>
    57ef:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    57f0:	48 39 ca             	cmp    %rcx,%rdx
    57f3:	7c 96                	jl     578b <overlap+0x5b>
    57f5:	4d 39 c1             	cmp    %r8,%r9
    57f8:	7d b4                	jge    57ae <overlap+0x7e>
    57fa:	48 39 ca             	cmp    %rcx,%rdx
    57fd:	74 93                	je     5792 <overlap+0x62>
    57ff:	eb d9                	jmp    57da <overlap+0xaa>
    5801:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5808:	c3                   	ret
    5809:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005810 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    5810:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    5814:	85 f6                	test   %esi,%esi
    5816:	0f 8e 59 03 00 00    	jle    5b75 <verify+0x365>
int verify(struct KernelThread *thread_data, int thread_count) {
    581c:	41 57                	push   %r15
    581e:	41 89 f7             	mov    %esi,%r15d
    5821:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    5823:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    5826:	41 55                	push   %r13
    5828:	41 54                	push   %r12
    582a:	55                   	push   %rbp
    582b:	53                   	push   %rbx
    582c:	48 8d 5f 20          	lea    0x20(%rdi),%rbx
    5830:	48 83 ec 48          	sub    $0x48,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    5834:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    5839:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    583e:	45 31 e4             	xor    %r12d,%r12d
    5841:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
      if (z != x)  {
    5846:	45 39 e6             	cmp    %r12d,%r14d
    5849:	0f 84 58 02 00 00    	je     5aa7 <verify+0x297>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    584f:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5854:	8b 50 08             	mov    0x8(%rax),%edx
    5857:	85 d2                	test   %edx,%edx
    5859:	0f 8e 48 02 00 00    	jle    5aa7 <verify+0x297>
    585f:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
    5867:	31 ed                	xor    %ebp,%ebp
    5869:	44 89 7c 24 30       	mov    %r15d,0x30(%rsp)
    586e:	45 89 f7             	mov    %r14d,%r15d
    5871:	41 89 ee             	mov    %ebp,%r14d
    5874:	44 89 fa             	mov    %r15d,%edx
    5877:	48 8d 35 96 09 00 00 	lea    0x996(%rip),%rsi        # 6214 <_IO_stdin_used+0x214>
    587e:	bf 01 00 00 00       	mov    $0x1,%edi
    5883:	31 c0                	xor    %eax,%eax
    5885:	e8 a6 cb ff ff       	call   2430 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    588a:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    588f:	8b 40 08             	mov    0x8(%rax),%eax
    5892:	85 c0                	test   %eax,%eax
    5894:	0f 8e ea 01 00 00    	jle    5a84 <verify+0x274>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    589a:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    589f:	44 89 74 24 34       	mov    %r14d,0x34(%rsp)
    58a4:	31 db                	xor    %ebx,%ebx
    58a6:	44 89 7c 24 38       	mov    %r15d,0x38(%rsp)
    58ab:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    58b0:	48 8b 28             	mov    (%rax),%rbp
    58b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    58b8:	4c 8b 6c 24 08       	mov    0x8(%rsp),%r13
    58bd:	48 8d 04 9b          	lea    (%rbx,%rbx,4),%rax
    58c1:	4c 8b 3c 24          	mov    (%rsp),%r15
    58c5:	48 8d 35 5d 09 00 00 	lea    0x95d(%rip),%rsi        # 6229 <_IO_stdin_used+0x229>
    58cc:	48 8d 04 43          	lea    (%rbx,%rax,2),%rax
    58d0:	bf 01 00 00 00       	mov    $0x1,%edi
    58d5:	49 89 c6             	mov    %rax,%r14
    58d8:	49 8b 45 00          	mov    0x0(%r13),%rax
    58dc:	4a 8b 8c 3d 00 04 00 00 	mov    0x400(%rbp,%r15,1),%rcx
    58e4:	49 c1 e6 07          	shl    $0x7,%r14
    58e8:	4a 8b 94 30 00 04 00 00 	mov    0x400(%rax,%r14,1),%rdx
    58f0:	31 c0                	xor    %eax,%eax
    58f2:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    58f7:	e8 34 cb ff ff       	call   2430 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    58fc:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5901:	48 8b 28             	mov    (%rax),%rbp
    5904:	4a 83 bc 3d 00 04 00 00 00 	cmpq   $0x0,0x400(%rbp,%r15,1)
    590d:	0f 8e 50 01 00 00    	jle    5a63 <verify+0x253>
    5913:	4d 03 75 00          	add    0x0(%r13),%r14
    5917:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    591c:	ba 01 00 00 00       	mov    $0x1,%edx
    5921:	4d 89 f5             	mov    %r14,%r13
    5924:	4d 8b b5 00 04 00 00 	mov    0x400(%r13),%r14
    592b:	4d 85 f6             	test   %r14,%r14
    592e:	0f 8e 2a 01 00 00    	jle    5a5e <verify+0x24e>
    5934:	0f 1f 40 00          	nopl   0x0(%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    5938:	49 89 d4             	mov    %rdx,%r12
    593b:	48 8b 04 24          	mov    (%rsp),%rax
    593f:	31 db                	xor    %ebx,%ebx
    5941:	4d 89 f2             	mov    %r14,%r10
    5944:	49 c1 e4 08          	shl    $0x8,%r12
    5948:	49 81 ec 00 01 00 00 	sub    $0x100,%r12
    594f:	4c 8d 7c 05 00       	lea    0x0(%rbp,%rax,1),%r15
    5954:	4d 89 e6             	mov    %r12,%r14
    5957:	49 89 dc             	mov    %rbx,%r12
    595a:	48 89 d3             	mov    %rdx,%rbx
    595d:	eb 2e                	jmp    598d <verify+0x17d>
    595f:	90                   	nop
  return left.tv_sec > right.tv_sec &&
    5960:	4c 39 c2             	cmp    %r8,%rdx
    5963:	0f 8d 67 01 00 00    	jge    5ad0 <verify+0x2c0>
    5969:	4c 39 df             	cmp    %r11,%rdi
    596c:	7e 05                	jle    5973 <verify+0x163>
    596e:	49 39 c1             	cmp    %rax,%r9
    5971:	7c 7d                	jl     59f0 <verify+0x1e0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5973:	4c 39 df             	cmp    %r11,%rdi
    5976:	0f 8d bb 01 00 00    	jge    5b37 <verify+0x327>
    597c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5980:	49 83 c4 01          	add    $0x1,%r12
    5984:	4d 39 d4             	cmp    %r10,%r12
    5987:	0f 8d b1 00 00 00    	jge    5a3e <verify+0x22e>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    598d:	49 8b 97 08 03 00 00 	mov    0x308(%r15),%rdx
    5994:	4c 89 e0             	mov    %r12,%rax
    5997:	48 c1 e0 08          	shl    $0x8,%rax
    599b:	49 03 85 08 03 00 00 	add    0x308(%r13),%rax
    59a2:	4c 01 f2             	add    %r14,%rdx
    59a5:	48 8b 08             	mov    (%rax),%rcx
    59a8:	48 8b b8 80 00 00 00 	mov    0x80(%rax),%rdi
    59af:	48 8b 32             	mov    (%rdx),%rsi
    59b2:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    59b6:	4c 8b 9a 80 00 00 00 	mov    0x80(%rdx),%r11
    59bd:	4c 8b 8a 88 00 00 00 	mov    0x88(%rdx),%r9
    59c4:	48 8b 50 08          	mov    0x8(%rax),%rdx
    59c8:	48 8b 80 88 00 00 00 	mov    0x88(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    59cf:	48 39 f1             	cmp    %rsi,%rcx
    59d2:	7c 8c                	jl     5960 <verify+0x150>
    59d4:	0f 8e 46 01 00 00    	jle    5b20 <verify+0x310>
    59da:	4c 39 c2             	cmp    %r8,%rdx
    59dd:	0f 8f fd 00 00 00    	jg     5ae0 <verify+0x2d0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    59e3:	75 9b                	jne    5980 <verify+0x170>
    59e5:	4c 39 df             	cmp    %r11,%rdi
    59e8:	7f 96                	jg     5980 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    59ea:	49 39 c1             	cmp    %rax,%r9
    59ed:	7c 91                	jl     5980 <verify+0x170>
    59ef:	90                   	nop
    59f0:	49 89 c1             	mov    %rax,%r9
    59f3:	48 89 f9             	mov    %rdi,%rcx
    59f6:	48 89 f2             	mov    %rsi,%rdx
    59f9:	bf 01 00 00 00       	mov    $0x1,%edi
    59fe:	48 8d 35 9b 0a 00 00 	lea    0xa9b(%rip),%rsi        # 64a0 <_IO_stdin_used+0x4a0>
    5a05:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5a07:	49 83 c4 01          	add    $0x1,%r12
    5a0b:	e8 20 ca ff ff       	call   2430 <__printf_chk@plt>
    5a10:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5a15:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    5a1a:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5a1d:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5a22:	4d 8b 95 00 04 00 00 	mov    0x400(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5a29:	48 8b 28             	mov    (%rax),%rbp
    5a2c:	48 8b 04 24          	mov    (%rsp),%rax
    5a30:	4c 8d 7c 05 00       	lea    0x0(%rbp,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5a35:	4d 39 d4             	cmp    %r10,%r12
    5a38:	0f 8c 4f ff ff ff    	jl     598d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    5a3e:	48 89 da             	mov    %rbx,%rdx
    5a41:	49 3b 9f 00 04 00 00 	cmp    0x400(%r15),%rbx
    5a48:	7d 14                	jge    5a5e <verify+0x24e>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    5a4a:	4d 8b b5 00 04 00 00 	mov    0x400(%r13),%r14
    5a51:	48 83 c2 01          	add    $0x1,%rdx
    5a55:	4d 85 f6             	test   %r14,%r14
    5a58:	0f 8f da fe ff ff    	jg     5938 <verify+0x128>
    5a5e:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    5a63:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5a68:	48 83 c3 01          	add    $0x1,%rbx
    5a6c:	39 58 08             	cmp    %ebx,0x8(%rax)
    5a6f:	0f 8f 43 fe ff ff    	jg     58b8 <verify+0xa8>
    5a75:	44 8b 74 24 34       	mov    0x34(%rsp),%r14d
    5a7a:	44 8b 7c 24 38       	mov    0x38(%rsp),%r15d
    5a7f:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    5a84:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5a89:	48 81 04 24 80 05 00 00 	addq   $0x580,(%rsp)
    5a91:	41 83 c6 01          	add    $0x1,%r14d
    5a95:	44 39 70 08          	cmp    %r14d,0x8(%rax)
    5a99:	0f 8f d5 fd ff ff    	jg     5874 <verify+0x64>
    5a9f:	45 89 fe             	mov    %r15d,%r14d
    5aa2:	44 8b 7c 24 30       	mov    0x30(%rsp),%r15d
    for (int z = 0 ; z < thread_count; z++) {
    5aa7:	48 81 44 24 08 00 03 00 00 	addq   $0x300,0x8(%rsp)
    5ab0:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    5ab5:	41 39 c7             	cmp    %eax,%r15d
    5ab8:	0f 84 87 00 00 00    	je     5b45 <verify+0x335>
    5abe:	41 89 c4             	mov    %eax,%r12d
    5ac1:	e9 80 fd ff ff       	jmp    5846 <verify+0x36>
    5ac6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5ad0:	0f 85 aa fe ff ff    	jne    5980 <verify+0x170>
    5ad6:	e9 98 fe ff ff       	jmp    5973 <verify+0x163>
    5adb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    5ae0:	49 39 c1             	cmp    %rax,%r9
    5ae3:	7e 09                	jle    5aee <verify+0x2de>
    5ae5:	4c 39 df             	cmp    %r11,%rdi
    5ae8:	0f 8c 02 ff ff ff    	jl     59f0 <verify+0x1e0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5aee:	4c 39 df             	cmp    %r11,%rdi
    5af1:	0f 8f 89 fe ff ff    	jg     5980 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5af7:	49 39 c1             	cmp    %rax,%r9
    5afa:	0f 8d f0 fe ff ff    	jge    59f0 <verify+0x1e0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    5b00:	48 39 f1             	cmp    %rsi,%rcx
    5b03:	0f 85 77 fe ff ff    	jne    5980 <verify+0x170>
    5b09:	4c 39 c2             	cmp    %r8,%rdx
    5b0c:	0f 85 6e fe ff ff    	jne    5980 <verify+0x170>
    5b12:	4c 39 df             	cmp    %r11,%rdi
    5b15:	0f 84 d5 fe ff ff    	je     59f0 <verify+0x1e0>
    5b1b:	e9 60 fe ff ff       	jmp    5980 <verify+0x170>
    5b20:	4c 39 c2             	cmp    %r8,%rdx
    5b23:	0f 8c 4a fe ff ff    	jl     5973 <verify+0x163>
    5b29:	4c 39 df             	cmp    %r11,%rdi
    5b2c:	7e c9                	jle    5af7 <verify+0x2e7>
    5b2e:	4c 39 c2             	cmp    %r8,%rdx
    5b31:	0f 85 49 fe ff ff    	jne    5980 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    5b37:	49 39 c1             	cmp    %rax,%r9
    5b3a:	0f 8f 40 fe ff ff    	jg     5980 <verify+0x170>
    5b40:	e9 ab fe ff ff       	jmp    59f0 <verify+0x1e0>
  for (int x = 0 ; x < thread_count; x++) {
    5b45:	48 81 44 24 10 00 03 00 00 	addq   $0x300,0x10(%rsp)
    5b4e:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    5b53:	41 8d 46 01          	lea    0x1(%r14),%eax
    5b57:	45 39 e6             	cmp    %r12d,%r14d
    5b5a:	74 08                	je     5b64 <verify+0x354>
    5b5c:	41 89 c6             	mov    %eax,%r14d
    5b5f:	e9 d5 fc ff ff       	jmp    5839 <verify+0x29>
}
    5b64:	48 83 c4 48          	add    $0x48,%rsp
    5b68:	31 c0                	xor    %eax,%eax
    5b6a:	5b                   	pop    %rbx
    5b6b:	5d                   	pop    %rbp
    5b6c:	41 5c                	pop    %r12
    5b6e:	41 5d                	pop    %r13
    5b70:	41 5e                	pop    %r14
    5b72:	41 5f                	pop    %r15
    5b74:	c3                   	ret
    5b75:	31 c0                	xor    %eax,%eax
    5b77:	c3                   	ret

Disassembly of section .fini:

0000000000005b78 <_fini>:
    5b78:	f3 0f 1e fa          	endbr64
    5b7c:	48 83 ec 08          	sub    $0x8,%rsp
    5b80:	48 83 c4 08          	add    $0x8,%rsp
    5b84:	c3                   	ret
