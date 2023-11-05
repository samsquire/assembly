
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
    26a1:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    26a6:	e8 d5 fc ff ff       	call   2380 <calloc@plt>
    26ab:	be 10 00 00 00       	mov    $0x10,%esi
    26b0:	bf 01 00 00 00       	mov    $0x1,%edi
    26b5:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    26ba:	e8 c1 fc ff ff       	call   2380 <calloc@plt>
    26bf:	be 10 00 00 00       	mov    $0x10,%esi
    26c4:	bf 01 00 00 00       	mov    $0x1,%edi
    26c9:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    26cf:	48 89 c3             	mov    %rax,%rbx
    26d2:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    26d7:	e8 a4 fc ff ff       	call   2380 <calloc@plt>
    26dc:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    26e1:	c7 44 24 30 00 00 00 00 	movl   $0x0,0x30(%rsp)
    26e9:	31 d2                	xor    %edx,%edx
    26eb:	48 89 43 08          	mov    %rax,0x8(%rbx)
    26ef:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    26f6:	4d 89 c7             	mov    %r8,%r15
    26f9:	4c 89 44 24 48       	mov    %r8,0x48(%rsp)
    26fe:	66 90                	xchg   %ax,%ax
    2700:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    2705:	41 89 17             	mov    %edx,(%r15)
    2708:	be 10 00 00 00       	mov    $0x10,%esi
    270d:	31 db                	xor    %ebx,%ebx
    270f:	41 c7 47 28 07 00 00 00 	movl   $0x7,0x28(%r15)
    2717:	bf 64 00 00 00       	mov    $0x64,%edi
    271c:	49 89 47 10          	mov    %rax,0x10(%r15)
    2720:	48 8b 05 d1 42 00 00 	mov    0x42d1(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
    2727:	89 54 24 08          	mov    %edx,0x8(%rsp)
    272b:	49 89 47 18          	mov    %rax,0x18(%r15)
    272f:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    2734:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    2739:	49 89 47 30          	mov    %rax,0x30(%r15)
    273d:	e8 3e fc ff ff       	call   2380 <calloc@plt>
    2742:	be 10 00 00 00       	mov    $0x10,%esi
    2747:	bf 64 00 00 00       	mov    $0x64,%edi
    274c:	49 89 47 50          	mov    %rax,0x50(%r15)
    2750:	e8 2b fc ff ff       	call   2380 <calloc@plt>
    2755:	be 28 00 00 00       	mov    $0x28,%esi
    275a:	bf 64 00 00 00       	mov    $0x64,%edi
    275f:	66 0f 6f 15 69 42 00 00 	movdqa 0x4269(%rip),%xmm2        # 69d0 <_IO_stdin_used+0x9d0>
    2767:	49 89 47 58          	mov    %rax,0x58(%r15)
    276b:	41 0f 11 57 68       	movups %xmm2,0x68(%r15)
    2770:	e8 0b fc ff ff       	call   2380 <calloc@plt>
    2775:	be 80 02 00 00       	mov    $0x280,%esi
    277a:	bf 07 00 00 00       	mov    $0x7,%edi
    277f:	66 0f 6f 1d 49 42 00 00 	movdqa 0x4249(%rip),%xmm3        # 69d0 <_IO_stdin_used+0x9d0>
    2787:	49 89 47 78          	mov    %rax,0x78(%r15)
    278b:	41 0f 11 9f 80 00 00 00 	movups %xmm3,0x80(%r15)
    2793:	e8 e8 fb ff ff       	call   2380 <calloc@plt>
    2798:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    279d:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    27a2:	49 89 47 20          	mov    %rax,0x20(%r15)
    27a6:	49 89 c7             	mov    %rax,%r15
    27a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    27b0:	4c 63 eb             	movslq %ebx,%r13
    27b3:	44 89 74 24 28       	mov    %r14d,0x28(%rsp)
    27b8:	4f 8d 64 ad 00       	lea    0x0(%r13,%r13,4),%r12
    27bd:	49 c1 e4 07          	shl    $0x7,%r12
    27c1:	44 39 f3             	cmp    %r14d,%ebx
    27c4:	0f 84 16 0a 00 00    	je     31e0 <main+0xc80>
    27ca:	be 20 00 00 00       	mov    $0x20,%esi
    27cf:	bf 06 00 00 00       	mov    $0x6,%edi
    27d4:	e8 a7 fb ff ff       	call   2380 <calloc@plt>
    27d9:	89 5c 24 18          	mov    %ebx,0x18(%rsp)
    27dd:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
    27e2:	48 8d a8 c0 00 00 00 	lea    0xc0(%rax),%rbp
    27e9:	4b 89 84 27 28 02 00 00 	mov    %rax,0x228(%r15,%r12,1)
    27f1:	49 89 c7             	mov    %rax,%r15
    27f4:	0f 1f 40 00          	nopl   0x0(%rax)
    27f8:	be 08 00 00 00       	mov    $0x8,%esi
    27fd:	bf 01 00 00 00       	mov    $0x1,%edi
    2802:	49 83 c7 20          	add    $0x20,%r15
    2806:	e8 75 fb ff ff       	call   2380 <calloc@plt>
    280b:	be 08 00 00 00       	mov    $0x8,%esi
    2810:	bf 01 00 00 00       	mov    $0x1,%edi
    2815:	49 89 c4             	mov    %rax,%r12
    2818:	e8 63 fb ff ff       	call   2380 <calloc@plt>
    281d:	be 00 01 00 00       	mov    $0x100,%esi
    2822:	bf 02 00 00 00       	mov    $0x2,%edi
    2827:	48 89 c3             	mov    %rax,%rbx
    282a:	e8 51 fb ff ff       	call   2380 <calloc@plt>
    282f:	66 0f 6f 05 a9 41 00 00 	movdqa 0x41a9(%rip),%xmm0        # 69e0 <_IO_stdin_used+0x9e0>
    2837:	48 8d b0 00 01 00 00 	lea    0x100(%rax),%rsi
    283e:	49 89 47 e0          	mov    %rax,-0x20(%r15)
    2842:	49 89 77 e8          	mov    %rsi,-0x18(%r15)
    2846:	4c 89 20             	mov    %r12,(%rax)
    2849:	48 89 98 00 01 00 00 	mov    %rbx,0x100(%rax)
    2850:	0f 29 80 80 00 00 00 	movaps %xmm0,0x80(%rax)
    2857:	0f 29 80 80 01 00 00 	movaps %xmm0,0x180(%rax)
    285e:	4c 39 fd             	cmp    %r15,%rbp
    2861:	75 95                	jne    27f8 <main+0x298>
    2863:	be 01 00 00 00       	mov    $0x1,%esi
    2868:	bf 00 01 00 00       	mov    $0x100,%edi
    286d:	8b 5c 24 18          	mov    0x18(%rsp),%ebx
    2871:	4c 8b 64 24 20       	mov    0x20(%rsp),%r12
    2876:	e8 05 fb ff ff       	call   2380 <calloc@plt>
    287b:	bf 18 00 00 00       	mov    $0x18,%edi
    2880:	48 89 c5             	mov    %rax,%rbp
    2883:	e8 68 fb ff ff       	call   23f0 <malloc@plt>
    2888:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    288d:	48 89 ef             	mov    %rbp,%rdi
    2890:	41 89 d9             	mov    %ebx,%r9d
    2893:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2898:	48 8d 0d e1 3c 00 00 	lea    0x3ce1(%rip),%rcx        # 6580 <_IO_stdin_used+0x580>
    289f:	ba 00 01 00 00       	mov    $0x100,%edx
    28a4:	31 c0                	xor    %eax,%eax
    28a6:	be 01 00 00 00       	mov    $0x1,%esi
    28ab:	e8 50 fc ff ff       	call   2500 <__sprintf_chk@plt>
    28b0:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    28b5:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    28ba:	ba ab aa aa aa       	mov    $0xaaaaaaab,%edx
    28bf:	be 20 00 00 00       	mov    $0x20,%esi
    28c4:	bf 3f 42 0f 00       	mov    $0xf423f,%edi
    28c9:	4d 89 6a 10          	mov    %r13,0x10(%r10)
    28cd:	44 8d 6b 01          	lea    0x1(%rbx),%r13d
    28d1:	4c 8b 78 20          	mov    0x20(%rax),%r15
    28d5:	44 89 e8             	mov    %r13d,%eax
    28d8:	44 89 e9             	mov    %r13d,%ecx
    28db:	49 89 2a             	mov    %rbp,(%r10)
    28de:	48 0f af c2          	imul   %rdx,%rax
    28e2:	4b 8d 2c 27          	lea    (%r15,%r12,1),%rbp
    28e6:	4d 89 72 08          	mov    %r14,0x8(%r10)
    28ea:	4c 89 95 40 02 00 00 	mov    %r10,0x240(%rbp)
    28f1:	48 c7 85 10 02 00 00 3f 42 0f 00 	movq   $0xf423f,0x210(%rbp)
    28fc:	48 c1 e8 22          	shr    $0x22,%rax
    2900:	8d 04 40             	lea    (%rax,%rax,2),%eax
    2903:	01 c0                	add    %eax,%eax
    2905:	29 c1                	sub    %eax,%ecx
    2907:	89 8d 48 02 00 00    	mov    %ecx,0x248(%rbp)
    290d:	e8 6e fa ff ff       	call   2380 <calloc@plt>
    2912:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    2916:	89 5d 00             	mov    %ebx,0x0(%rbp)
    2919:	48 89 85 08 02 00 00 	mov    %rax,0x208(%rbp)
    2920:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    2925:	48 c7 85 18 02 00 00 00 00 00 00 	movq   $0x0,0x218(%rbp)
    2930:	48 89 85 28 01 00 00 	mov    %rax,0x128(%rbp)
    2937:	48 8b 05 c2 40 00 00 	mov    0x40c2(%rip),%rax        # 6a00 <_IO_stdin_used+0xa00>
    293e:	89 8d 30 01 00 00    	mov    %ecx,0x130(%rbp)
    2944:	48 89 85 80 01 00 00 	mov    %rax,0x180(%rbp)
    294b:	48 b8 01 00 00 00 06 00 00 00 	movabs $0x600000001,%rax
    2955:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
    295f:	c7 85 34 01 00 00 06 00 00 00 	movl   $0x6,0x134(%rbp)
    2969:	48 89 85 38 02 00 00 	mov    %rax,0x238(%rbp)
    2970:	83 fb 05             	cmp    $0x5,%ebx
    2973:	0f 84 47 08 00 00    	je     31c0 <main+0xc60>
    2979:	8b 44 24 28          	mov    0x28(%rsp),%eax
    297d:	39 c3                	cmp    %eax,%ebx
    297f:	75 57                	jne    29d8 <main+0x478>
    2981:	8b 74 24 30          	mov    0x30(%rsp),%esi
    2985:	85 f6                	test   %esi,%esi
    2987:	75 4f                	jne    29d8 <main+0x478>
    2989:	89 ca                	mov    %ecx,%edx
    298b:	48 8d 35 16 3c 00 00 	lea    0x3c16(%rip),%rsi        # 65a8 <_IO_stdin_used+0x5a8>
    2992:	bf 01 00 00 00       	mov    $0x1,%edi
    2997:	31 c0                	xor    %eax,%eax
    2999:	e8 92 fa ff ff       	call   2430 <__printf_chk@plt>
    299e:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    29a3:	48 8b 4c 24 38       	mov    0x38(%rsp),%rcx
    29a8:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    29b0:	4c 8b 78 20          	mov    0x20(%rax),%r15
    29b4:	48 89 48 38          	mov    %rcx,0x38(%rax)
    29b8:	48 8d 05 01 2c 00 00 	lea    0x2c01(%rip),%rax        # 55c0 <barriered_work_ingest>
    29bf:	4b 89 84 27 18 01 00 00 	mov    %rax,0x118(%r15,%r12,1)
    29c7:	41 83 fd 07          	cmp    $0x7,%r13d
    29cb:	74 1f                	je     29ec <main+0x48c>
    29cd:	44 89 eb             	mov    %r13d,%ebx
    29d0:	e9 db fd ff ff       	jmp    27b0 <main+0x250>
    29d5:	0f 1f 00             	nopl   (%rax)
    29d8:	48 8d 05 71 28 00 00 	lea    0x2871(%rip),%rax        # 5250 <barriered_work>
    29df:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
    29e6:	41 83 fd 07          	cmp    $0x7,%r13d
    29ea:	75 e1                	jne    29cd <main+0x46d>
    29ec:	4c 89 f2             	mov    %r14,%rdx
    29ef:	48 8d 05 3a 09 00 00 	lea    0x93a(%rip),%rax        # 3330 <barriered_reset>
    29f6:	4d 89 fe             	mov    %r15,%r14
    29f9:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    29fe:	49 89 86 18 10 00 00 	mov    %rax,0x1018(%r14)
    2a05:	8b 44 24 08          	mov    0x8(%rsp),%eax
    2a09:	48 83 c2 01          	add    $0x1,%rdx
    2a0d:	4d 89 be 28 10 00 00 	mov    %r15,0x1028(%r14)
    2a14:	49 81 c7 98 00 00 00 	add    $0x98,%r15
    2a1b:	41 89 86 30 10 00 00 	mov    %eax,0x1030(%r14)
    2a22:	48 8b 05 d7 3f 00 00 	mov    0x3fd7(%rip),%rax        # 6a00 <_IO_stdin_used+0xa00>
    2a29:	41 c7 86 80 0f 00 00 00 00 00 00 	movl   $0x0,0xf80(%r14)
    2a34:	41 c7 86 00 0f 00 00 06 00 00 00 	movl   $0x6,0xf00(%r14)
    2a3f:	41 c7 86 34 10 00 00 06 00 00 00 	movl   $0x6,0x1034(%r14)
    2a4a:	41 c7 86 3c 11 00 00 06 00 00 00 	movl   $0x6,0x113c(%r14)
    2a55:	49 89 86 80 10 00 00 	mov    %rax,0x1080(%r14)
    2a5c:	48 83 fa 09          	cmp    $0x9,%rdx
    2a60:	0f 85 9a fc ff ff    	jne    2700 <main+0x1a0>
    2a66:	4c 8b 44 24 48       	mov    0x48(%rsp),%r8
    2a6b:	be 38 00 00 00       	mov    $0x38,%esi
    2a70:	bf 09 00 00 00       	mov    $0x9,%edi
    2a75:	45 31 ed             	xor    %r13d,%r13d
    2a78:	4c 8d 3d 41 09 00 00 	lea    0x941(%rip),%r15        # 33c0 <barriered_thread>
    2a7f:	49 8d 80 28 04 00 00 	lea    0x428(%r8),%rax
    2a86:	4c 89 44 24 20       	mov    %r8,0x20(%rsp)
    2a8b:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2a90:	49 8b 40 20          	mov    0x20(%r8),%rax
    2a94:	4d 89 80 38 04 00 00 	mov    %r8,0x438(%r8)
    2a9b:	41 c7 80 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r8)
    2aa6:	41 c7 80 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r8)
    2ab1:	41 c7 80 50 04 00 00 07 00 00 00 	movl   $0x7,0x450(%r8)
    2abc:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
    2ac6:	49 8b 80 b8 00 00 00 	mov    0xb8(%r8),%rax
    2acd:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
    2ad7:	49 8b 80 50 01 00 00 	mov    0x150(%r8),%rax
    2ade:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
    2ae8:	49 8b 80 e8 01 00 00 	mov    0x1e8(%r8),%rax
    2aef:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
    2af9:	49 8b 80 80 02 00 00 	mov    0x280(%r8),%rax
    2b00:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
    2b0a:	49 8b 80 18 03 00 00 	mov    0x318(%r8),%rax
    2b11:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
    2b1b:	e8 60 f8 ff ff       	call   2380 <calloc@plt>
    2b20:	be 38 00 00 00       	mov    $0x38,%esi
    2b25:	bf 09 00 00 00       	mov    $0x9,%edi
    2b2a:	48 89 c3             	mov    %rax,%rbx
    2b2d:	e8 4e f8 ff ff       	call   2380 <calloc@plt>
    2b32:	be 38 00 00 00       	mov    $0x38,%esi
    2b37:	bf 09 00 00 00       	mov    $0x9,%edi
    2b3c:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2b41:	e8 3a f8 ff ff       	call   2380 <calloc@plt>
    2b46:	be 08 00 00 00       	mov    $0x8,%esi
    2b4b:	bf 09 00 00 00       	mov    $0x9,%edi
    2b50:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2b55:	e8 26 f8 ff ff       	call   2380 <calloc@plt>
    2b5a:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    2b5f:	ba 06 00 00 00       	mov    $0x6,%edx
    2b64:	48 8d 35 84 37 00 00 	lea    0x3784(%rip),%rsi        # 62ef <_IO_stdin_used+0x2ef>
    2b6b:	49 89 c4             	mov    %rax,%r12
    2b6e:	48 8b 05 93 3e 00 00 	mov    0x3e93(%rip),%rax        # 6a08 <_IO_stdin_used+0xa08>
    2b75:	bf 01 00 00 00       	mov    $0x1,%edi
    2b7a:	4d 89 80 a0 03 00 00 	mov    %r8,0x3a0(%r8)
    2b81:	4c 89 e5             	mov    %r12,%rbp
    2b84:	49 89 80 b8 03 00 00 	mov    %rax,0x3b8(%r8)
    2b8b:	31 c0                	xor    %eax,%eax
    2b8d:	41 c7 80 a8 03 00 00 06 00 00 00 	movl   $0x6,0x3a8(%r8)
    2b98:	49 c7 80 90 03 00 00 00 00 00 00 	movq   $0x0,0x390(%r8)
    2ba3:	e8 88 f8 ff ff       	call   2430 <__printf_chk@plt>
    2ba8:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    2bad:	49 8d 7c 24 30       	lea    0x30(%r12),%rdi
    2bb2:	45 89 ec             	mov    %r13d,%r12d
    2bb5:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
    2bbc:	48 8d 15 ad 0b 00 00 	lea    0xbad(%rip),%rdx        # 3770 <timer_thread>
    2bc3:	49 89 ed             	mov    %rbp,%r13
    2bc6:	49 8d 88 90 03 00 00 	lea    0x390(%r8),%rcx
    2bcd:	e8 7e f8 ff ff       	call   2450 <pthread_create@plt>
    2bd2:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
    2bd7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    2be0:	41 c7 46 04 01 00 00 00 	movl   $0x1,0x4(%r14)
    2be8:	44 89 e2             	mov    %r12d,%edx
    2beb:	bf 01 00 00 00       	mov    $0x1,%edi
    2bf0:	31 c0                	xor    %eax,%eax
    2bf2:	41 c7 46 2c 01 00 00 00 	movl   $0x1,0x2c(%r14)
    2bfa:	48 8d 35 c7 39 00 00 	lea    0x39c7(%rip),%rsi        # 65c8 <_IO_stdin_used+0x5c8>
    2c01:	41 83 c4 01          	add    $0x1,%r12d
    2c05:	e8 26 f8 ff ff       	call   2430 <__printf_chk@plt>
    2c0a:	4c 89 f1             	mov    %r14,%rcx
    2c0d:	48 89 de             	mov    %rbx,%rsi
    2c10:	48 89 ef             	mov    %rbp,%rdi
    2c13:	4c 89 fa             	mov    %r15,%rdx
    2c16:	49 81 c6 98 00 00 00 	add    $0x98,%r14
    2c1d:	48 83 c5 08          	add    $0x8,%rbp
    2c21:	48 83 c3 38          	add    $0x38,%rbx
    2c25:	e8 26 f8 ff ff       	call   2450 <pthread_create@plt>
    2c2a:	41 83 fc 06          	cmp    $0x6,%r12d
    2c2e:	75 b0                	jne    2be0 <main+0x680>
    2c30:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    2c35:	48 8b 1d d4 3d 00 00 	mov    0x3dd4(%rip),%rbx        # 6a10 <_IO_stdin_used+0xa10>
    2c3c:	be d8 00 00 00       	mov    $0xd8,%esi
    2c41:	4d 89 ec             	mov    %r13,%r12
    2c44:	bf 01 00 00 00       	mov    $0x1,%edi
    2c49:	48 8d 2d 0f 37 00 00 	lea    0x370f(%rip),%rbp        # 635f <_IO_stdin_used+0x35f>
    2c50:	49 89 98 50 04 00 00 	mov    %rbx,0x450(%r8)
    2c57:	41 c7 80 2c 04 00 00 02 00 00 00 	movl   $0x2,0x42c(%r8)
    2c62:	e8 19 f7 ff ff       	call   2380 <calloc@plt>
    2c67:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    2c6c:	be 00 08 00 00       	mov    $0x800,%esi
    2c71:	31 ff                	xor    %edi,%edi
    2c73:	49 89 80 68 04 00 00 	mov    %rax,0x468(%r8)
    2c7a:	e8 11 f8 ff ff       	call   2490 <eventfd@plt>
    2c7f:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    2c84:	ba 07 00 00 00       	mov    $0x7,%edx
    2c89:	48 8d 35 7d 36 00 00 	lea    0x367d(%rip),%rsi        # 630d <_IO_stdin_used+0x30d>
    2c90:	bf 01 00 00 00       	mov    $0x1,%edi
    2c95:	41 89 80 70 04 00 00 	mov    %eax,0x470(%r8)
    2c9c:	31 c0                	xor    %eax,%eax
    2c9e:	4d 89 80 38 04 00 00 	mov    %r8,0x438(%r8)
    2ca5:	41 c7 80 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r8)
    2cb0:	41 c7 80 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r8)
    2cbb:	e8 70 f7 ff ff       	call   2430 <__printf_chk@plt>
    2cc0:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    2cc5:	49 8d 7d 38          	lea    0x38(%r13),%rdi
    2cc9:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    2cce:	48 8d 15 2b 1d 00 00 	lea    0x1d2b(%rip),%rdx        # 4a00 <io_thread>
    2cd5:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    2cdc:	e8 6f f7 ff ff       	call   2450 <pthread_create@plt>
    2ce1:	ba 08 00 00 00       	mov    $0x8,%edx
    2ce6:	48 8d 35 37 36 00 00 	lea    0x3637(%rip),%rsi        # 6324 <_IO_stdin_used+0x324>
    2ced:	31 c0                	xor    %eax,%eax
    2cef:	bf 01 00 00 00       	mov    $0x1,%edi
    2cf4:	e8 37 f7 ff ff       	call   2430 <__printf_chk@plt>
    2cf9:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
    2cfe:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    2d03:	49 8d 7d 40          	lea    0x40(%r13),%rdi
    2d07:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    2d0c:	48 8d 15 9d 09 00 00 	lea    0x99d(%rip),%rdx        # 36b0 <external_thread>
    2d13:	4c 8d 6c 24 50       	lea    0x50(%rsp),%r13
    2d18:	49 89 80 f8 04 00 00 	mov    %rax,0x4f8(%r8)
    2d1f:	48 8b 05 d2 3c 00 00 	mov    0x3cd2(%rip),%rax        # 69f8 <_IO_stdin_used+0x9f8>
    2d26:	49 8d 88 c0 04 00 00 	lea    0x4c0(%r8),%rcx
    2d2d:	49 89 98 e8 04 00 00 	mov    %rbx,0x4e8(%r8)
    2d34:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
    2d3b:	31 db                	xor    %ebx,%ebx
    2d3d:	49 89 80 d8 04 00 00 	mov    %rax,0x4d8(%r8)
    2d44:	48 8b 05 cd 3c 00 00 	mov    0x3ccd(%rip),%rax        # 6a18 <_IO_stdin_used+0xa18>
    2d4b:	4d 89 80 d0 04 00 00 	mov    %r8,0x4d0(%r8)
    2d52:	49 89 80 c0 04 00 00 	mov    %rax,0x4c0(%r8)
    2d59:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    2d5e:	e8 ed f6 ff ff       	call   2450 <pthread_create@plt>
    2d63:	48 8d 3d d7 35 00 00 	lea    0x35d7(%rip),%rdi        # 6341 <_IO_stdin_used+0x341>
    2d6a:	e8 61 f5 ff ff       	call   22d0 <puts@plt>
    2d6f:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    2d74:	0f 1f 40 00          	nopl   0x0(%rax)
    2d78:	49 8b 3c dc          	mov    (%r12,%rbx,8),%rdi
    2d7c:	4c 89 ee             	mov    %r13,%rsi
    2d7f:	e8 4c f7 ff ff       	call   24d0 <pthread_join@plt>
    2d84:	89 da                	mov    %ebx,%edx
    2d86:	48 89 ee             	mov    %rbp,%rsi
    2d89:	bf 01 00 00 00       	mov    $0x1,%edi
    2d8e:	31 c0                	xor    %eax,%eax
    2d90:	48 83 c3 01          	add    $0x1,%rbx
    2d94:	e8 97 f6 ff ff       	call   2430 <__printf_chk@plt>
    2d99:	48 83 fb 09          	cmp    $0x9,%rbx
    2d9d:	75 d9                	jne    2d78 <main+0x818>
    2d9f:	49 8d 86 b0 03 00 00 	lea    0x3b0(%r14),%rax
    2da6:	31 ed                	xor    %ebp,%ebp
    2da8:	31 c9                	xor    %ecx,%ecx
    2daa:	45 31 db             	xor    %r11d,%r11d
    2dad:	45 31 c9             	xor    %r9d,%r9d
    2db0:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    2db5:	45 31 e4             	xor    %r12d,%r12d
    2db8:	4d 8d 6e 20          	lea    0x20(%r14),%r13
    2dbc:	48 89 6c 24 08       	mov    %rbp,0x8(%rsp)
    2dc1:	31 db                	xor    %ebx,%ebx
    2dc3:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2dc8:	4c 89 5c 24 18       	mov    %r11,0x18(%rsp)
    2dcd:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    2dd2:	4c 89 74 24 30       	mov    %r14,0x30(%rsp)
    2dd7:	4d 89 e6             	mov    %r12,%r14
    2dda:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    2de0:	49 63 45 08          	movslq 0x8(%r13),%rax
    2de4:	85 c0                	test   %eax,%eax
    2de6:	0f 8e af 00 00 00    	jle    2e9b <main+0x93b>
    2dec:	49 8b 4d 00          	mov    0x0(%r13),%rcx
    2df0:	48 8d 34 80          	lea    (%rax,%rax,4),%rsi
    2df4:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    2df9:	48 c1 e6 07          	shl    $0x7,%rsi
    2dfd:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    2e02:	4c 8b 4c 24 20       	mov    0x20(%rsp),%r9
    2e07:	48 8d 91 08 01 00 00 	lea    0x108(%rcx),%rdx
    2e0e:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    2e13:	48 01 d6             	add    %rdx,%rsi
    2e16:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    2e20:	4c 03 32             	add    (%rdx),%r14
    2e23:	48 8b 82 20 01 00 00 	mov    0x120(%rdx),%rax
    2e2a:	48 81 c2 80 02 00 00 	add    $0x280,%rdx
    2e31:	48 03 8a 88 fd ff ff 	add    -0x278(%rdx),%rcx
    2e38:	4c 03 9a 98 fe ff ff 	add    -0x168(%rdx),%r11
    2e3f:	48 03 68 10          	add    0x10(%rax),%rbp
    2e43:	48 03 58 18          	add    0x18(%rax),%rbx
    2e47:	48 03 68 30          	add    0x30(%rax),%rbp
    2e4b:	48 03 58 38          	add    0x38(%rax),%rbx
    2e4f:	48 03 68 50          	add    0x50(%rax),%rbp
    2e53:	48 03 58 58          	add    0x58(%rax),%rbx
    2e57:	48 03 68 70          	add    0x70(%rax),%rbp
    2e5b:	48 03 58 78          	add    0x78(%rax),%rbx
    2e5f:	48 03 a8 90 00 00 00 	add    0x90(%rax),%rbp
    2e66:	48 03 98 98 00 00 00 	add    0x98(%rax),%rbx
    2e6d:	4c 03 8a a8 fe ff ff 	add    -0x158(%rdx),%r9
    2e74:	48 03 a8 b0 00 00 00 	add    0xb0(%rax),%rbp
    2e7b:	48 03 98 b8 00 00 00 	add    0xb8(%rax),%rbx
    2e82:	48 39 f2             	cmp    %rsi,%rdx
    2e85:	75 99                	jne    2e20 <main+0x8c0>
    2e87:	48 89 6c 24 08       	mov    %rbp,0x8(%rsp)
    2e8c:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    2e91:	4c 89 5c 24 18       	mov    %r11,0x18(%rsp)
    2e96:	4c 89 4c 24 20       	mov    %r9,0x20(%rsp)
    2e9b:	45 31 e4             	xor    %r12d,%r12d
    2e9e:	49 83 7d 50 00       	cmpq   $0x0,0x50(%r13)
    2ea3:	7e 79                	jle    2f1e <main+0x9be>
    2ea5:	4c 89 ed             	mov    %r13,%rbp
    2ea8:	49 89 dd             	mov    %rbx,%r13
    2eab:	4c 89 e3             	mov    %r12,%rbx
    2eae:	66 90                	xchg   %ax,%ax
    2eb0:	48 8b 7d 30          	mov    0x30(%rbp),%rdi
    2eb4:	48 89 de             	mov    %rbx,%rsi
    2eb7:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
    2ec1:	48 83 c3 01          	add    $0x1,%rbx
    2ec5:	48 c1 e6 04          	shl    $0x4,%rsi
    2ec9:	48 01 f7             	add    %rsi,%rdi
    2ecc:	48 03 75 38          	add    0x38(%rbp),%rsi
    2ed0:	48 8b 56 08          	mov    0x8(%rsi),%rdx
    2ed4:	48 2b 57 08          	sub    0x8(%rdi),%rdx
    2ed8:	48 f7 e2             	mul    %rdx
    2edb:	31 c0                	xor    %eax,%eax
    2edd:	48 89 d1             	mov    %rdx,%rcx
    2ee0:	48 8b 16             	mov    (%rsi),%rdx
    2ee3:	48 8d 35 89 34 00 00 	lea    0x3489(%rip),%rsi        # 6373 <_IO_stdin_used+0x373>
    2eea:	48 2b 17             	sub    (%rdi),%rdx
    2eed:	48 c1 e9 12          	shr    $0x12,%rcx
    2ef1:	bf 01 00 00 00       	mov    $0x1,%edi
    2ef6:	e8 35 f5 ff ff       	call   2430 <__printf_chk@plt>
    2efb:	48 8b 55 40          	mov    0x40(%rbp),%rdx
    2eff:	bf 01 00 00 00       	mov    $0x1,%edi
    2f04:	31 c0                	xor    %eax,%eax
    2f06:	48 8d 35 84 34 00 00 	lea    0x3484(%rip),%rsi        # 6391 <_IO_stdin_used+0x391>
    2f0d:	e8 1e f5 ff ff       	call   2430 <__printf_chk@plt>
    2f12:	48 39 5d 50          	cmp    %rbx,0x50(%rbp)
    2f16:	7f 98                	jg     2eb0 <main+0x950>
    2f18:	4c 89 eb             	mov    %r13,%rbx
    2f1b:	49 89 ed             	mov    %rbp,%r13
    2f1e:	49 bf ab aa aa aa aa aa aa aa 	movabs $0xaaaaaaaaaaaaaaab,%r15
    2f28:	45 31 e4             	xor    %r12d,%r12d
    2f2b:	49 83 7d 68 00       	cmpq   $0x0,0x68(%r13)
    2f30:	0f 8e 92 00 00 00    	jle    2fc8 <main+0xa68>
    2f36:	4c 89 e8             	mov    %r13,%rax
    2f39:	49 89 dd             	mov    %rbx,%r13
    2f3c:	4c 89 e3             	mov    %r12,%rbx
    2f3f:	49 89 c4             	mov    %rax,%r12
    2f42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    2f48:	49 8b 44 24 58       	mov    0x58(%r12),%rax
    2f4d:	48 8d 14 9b          	lea    (%rbx,%rbx,4),%rdx
    2f51:	48 83 ec 08          	sub    $0x8,%rsp
    2f55:	48 8d 35 94 36 00 00 	lea    0x3694(%rip),%rsi        # 65f0 <_IO_stdin_used+0x5f0>
    2f5c:	bf 01 00 00 00       	mov    $0x1,%edi
    2f61:	48 83 c3 01          	add    $0x1,%rbx
    2f65:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    2f69:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
    2f73:	48 8b 69 18          	mov    0x18(%rcx),%rbp
    2f77:	48 2b 69 08          	sub    0x8(%rcx),%rbp
    2f7b:	48 f7 e5             	mul    %rbp
    2f7e:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    2f82:	4c 2b 01             	sub    (%rcx),%r8
    2f85:	31 c0                	xor    %eax,%eax
    2f87:	8b 49 20             	mov    0x20(%rcx),%ecx
    2f8a:	55                   	push   %rbp
    2f8b:	48 c1 ea 12          	shr    $0x12,%rdx
    2f8f:	49 89 d1             	mov    %rdx,%r9
    2f92:	ba 06 00 00 00       	mov    $0x6,%edx
    2f97:	e8 94 f4 ff ff       	call   2430 <__printf_chk@plt>
    2f9c:	48 89 e8             	mov    %rbp,%rax
    2f9f:	bf 01 00 00 00       	mov    $0x1,%edi
    2fa4:	48 8d 35 02 34 00 00 	lea    0x3402(%rip),%rsi        # 63ad <_IO_stdin_used+0x3ad>
    2fab:	49 f7 e7             	mul    %r15
    2fae:	31 c0                	xor    %eax,%eax
    2fb0:	48 c1 ea 02          	shr    $0x2,%rdx
    2fb4:	e8 77 f4 ff ff       	call   2430 <__printf_chk@plt>
    2fb9:	58                   	pop    %rax
    2fba:	5a                   	pop    %rdx
    2fbb:	49 3b 5c 24 68       	cmp    0x68(%r12),%rbx
    2fc0:	7c 86                	jl     2f48 <main+0x9e8>
    2fc2:	4c 89 eb             	mov    %r13,%rbx
    2fc5:	4d 89 e5             	mov    %r12,%r13
    2fc8:	49 8b 55 70          	mov    0x70(%r13),%rdx
    2fcc:	48 8d 35 ce 33 00 00 	lea    0x33ce(%rip),%rsi        # 63a1 <_IO_stdin_used+0x3a1>
    2fd3:	bf 01 00 00 00       	mov    $0x1,%edi
    2fd8:	31 c0                	xor    %eax,%eax
    2fda:	49 81 c5 98 00 00 00 	add    $0x98,%r13
    2fe1:	e8 4a f4 ff ff       	call   2430 <__printf_chk@plt>
    2fe6:	4c 39 6c 24 28       	cmp    %r13,0x28(%rsp)
    2feb:	0f 85 ef fd ff ff    	jne    2de0 <main+0x880>
    2ff1:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2ff6:	4c 8b 44 24 30       	mov    0x30(%rsp),%r8
    2ffb:	4c 89 f2             	mov    %r14,%rdx
    2ffe:	31 c0                	xor    %eax,%eax
    3000:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    3005:	48 8d 35 b3 33 00 00 	lea    0x33b3(%rip),%rsi        # 63bf <_IO_stdin_used+0x3bf>
    300c:	bf 01 00 00 00       	mov    $0x1,%edi
    3011:	4d 89 f4             	mov    %r14,%r12
    3014:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    3019:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    301e:	49 bd 89 88 88 88 88 88 88 88 	movabs $0x8888888888888889,%r13
    3028:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    302d:	4c 89 5c 24 10       	mov    %r11,0x10(%rsp)
    3032:	e8 f9 f3 ff ff       	call   2430 <__printf_chk@plt>
    3037:	bf 0a 00 00 00       	mov    $0xa,%edi
    303c:	e8 7f f2 ff ff       	call   22c0 <putchar@plt>
    3041:	4c 8b 74 24 40       	mov    0x40(%rsp),%r14
    3046:	48 8d 35 86 33 00 00 	lea    0x3386(%rip),%rsi        # 63d3 <_IO_stdin_used+0x3d3>
    304d:	31 c0                	xor    %eax,%eax
    304f:	bf 01 00 00 00       	mov    $0x1,%edi
    3054:	49 8b 16             	mov    (%r14),%rdx
    3057:	e8 d4 f3 ff ff       	call   2430 <__printf_chk@plt>
    305c:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    3061:	48 8d 35 80 33 00 00 	lea    0x3380(%rip),%rsi        # 63e8 <_IO_stdin_used+0x3e8>
    3068:	31 c0                	xor    %eax,%eax
    306a:	bf 01 00 00 00       	mov    $0x1,%edi
    306f:	e8 bc f3 ff ff       	call   2430 <__printf_chk@plt>
    3074:	bf 0a 00 00 00       	mov    $0xa,%edi
    3079:	e8 42 f2 ff ff       	call   22c0 <putchar@plt>
    307e:	49 8b 36             	mov    (%r14),%rsi
    3081:	bf 01 00 00 00       	mov    $0x1,%edi
    3086:	48 89 f0             	mov    %rsi,%rax
    3089:	49 f7 ed             	imul   %r13
    308c:	31 c0                	xor    %eax,%eax
    308e:	48 01 f2             	add    %rsi,%rdx
    3091:	48 c1 fe 3f          	sar    $0x3f,%rsi
    3095:	48 c1 fa 04          	sar    $0x4,%rdx
    3099:	48 29 f2             	sub    %rsi,%rdx
    309c:	48 8d 35 85 35 00 00 	lea    0x3585(%rip),%rsi        # 6628 <_IO_stdin_used+0x628>
    30a3:	e8 88 f3 ff ff       	call   2430 <__printf_chk@plt>
    30a8:	49 8b 56 08          	mov    0x8(%r14),%rdx
    30ac:	bf 01 00 00 00       	mov    $0x1,%edi
    30b1:	31 c0                	xor    %eax,%eax
    30b3:	48 8d 35 8e 35 00 00 	lea    0x358e(%rip),%rsi        # 6648 <_IO_stdin_used+0x648>
    30ba:	e8 71 f3 ff ff       	call   2430 <__printf_chk@plt>
    30bf:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    30c4:	bf 01 00 00 00       	mov    $0x1,%edi
    30c9:	48 8d 35 a0 35 00 00 	lea    0x35a0(%rip),%rsi        # 6670 <_IO_stdin_used+0x670>
    30d0:	4c 89 d8             	mov    %r11,%rax
    30d3:	49 f7 ed             	imul   %r13
    30d6:	31 c0                	xor    %eax,%eax
    30d8:	4c 01 da             	add    %r11,%rdx
    30db:	49 c1 fb 3f          	sar    $0x3f,%r11
    30df:	48 c1 fa 04          	sar    $0x4,%rdx
    30e3:	4c 29 da             	sub    %r11,%rdx
    30e6:	e8 45 f3 ff ff       	call   2430 <__printf_chk@plt>
    30eb:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    30f0:	bf 01 00 00 00       	mov    $0x1,%edi
    30f5:	48 8d 35 a4 35 00 00 	lea    0x35a4(%rip),%rsi        # 66a0 <_IO_stdin_used+0x6a0>
    30fc:	48 89 c8             	mov    %rcx,%rax
    30ff:	49 f7 ed             	imul   %r13
    3102:	31 c0                	xor    %eax,%eax
    3104:	48 01 ca             	add    %rcx,%rdx
    3107:	48 c1 f9 3f          	sar    $0x3f,%rcx
    310b:	48 c1 fa 04          	sar    $0x4,%rdx
    310f:	48 29 ca             	sub    %rcx,%rdx
    3112:	e8 19 f3 ff ff       	call   2430 <__printf_chk@plt>
    3117:	4c 89 e0             	mov    %r12,%rax
    311a:	bf 01 00 00 00       	mov    $0x1,%edi
    311f:	48 8d 35 aa 35 00 00 	lea    0x35aa(%rip),%rsi        # 66d0 <_IO_stdin_used+0x6d0>
    3126:	49 f7 ed             	imul   %r13
    3129:	4c 01 e2             	add    %r12,%rdx
    312c:	49 c1 fc 3f          	sar    $0x3f,%r12
    3130:	31 c0                	xor    %eax,%eax
    3132:	48 c1 fa 04          	sar    $0x4,%rdx
    3136:	4c 29 e2             	sub    %r12,%rdx
    3139:	e8 f2 f2 ff ff       	call   2430 <__printf_chk@plt>
    313e:	48 89 e8             	mov    %rbp,%rax
    3141:	bf 01 00 00 00       	mov    $0x1,%edi
    3146:	48 8d 35 a8 32 00 00 	lea    0x32a8(%rip),%rsi        # 63f5 <_IO_stdin_used+0x3f5>
    314d:	49 f7 ed             	imul   %r13
    3150:	31 c0                	xor    %eax,%eax
    3152:	48 01 ea             	add    %rbp,%rdx
    3155:	48 c1 fd 3f          	sar    $0x3f,%rbp
    3159:	48 c1 fa 04          	sar    $0x4,%rdx
    315d:	48 29 ea             	sub    %rbp,%rdx
    3160:	e8 cb f2 ff ff       	call   2430 <__printf_chk@plt>
    3165:	48 89 d8             	mov    %rbx,%rax
    3168:	bf 01 00 00 00       	mov    $0x1,%edi
    316d:	48 8d 35 92 32 00 00 	lea    0x3292(%rip),%rsi        # 6406 <_IO_stdin_used+0x406>
    3174:	49 f7 ed             	imul   %r13
    3177:	31 c0                	xor    %eax,%eax
    3179:	48 01 da             	add    %rbx,%rdx
    317c:	48 c1 fb 3f          	sar    $0x3f,%rbx
    3180:	48 c1 fa 04          	sar    $0x4,%rdx
    3184:	48 29 da             	sub    %rbx,%rdx
    3187:	e8 a4 f2 ff ff       	call   2430 <__printf_chk@plt>
    318c:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    3191:	be 06 00 00 00       	mov    $0x6,%esi
    3196:	e8 c5 25 00 00       	call   5760 <verify>
    319b:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    31a0:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    31a9:	75 49                	jne    31f4 <main+0xc94>
    31ab:	48 83 c4 68          	add    $0x68,%rsp
    31af:	31 c0                	xor    %eax,%eax
    31b1:	5b                   	pop    %rbx
    31b2:	5d                   	pop    %rbp
    31b3:	41 5c                	pop    %r12
    31b5:	41 5d                	pop    %r13
    31b7:	41 5e                	pop    %r14
    31b9:	41 5f                	pop    %r15
    31bb:	c3                   	ret
    31bc:	0f 1f 40 00          	nopl   0x0(%rax)
    31c0:	48 8d 05 89 20 00 00 	lea    0x2089(%rip),%rax        # 5250 <barriered_work>
    31c7:	41 bd 06 00 00 00    	mov    $0x6,%r13d
    31cd:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
    31d4:	e9 f4 f7 ff ff       	jmp    29cd <main+0x46d>
    31d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    31e0:	48 8d 05 09 01 00 00 	lea    0x109(%rip),%rax        # 32f0 <do_protected_write>
    31e7:	4b 89 84 27 20 01 00 00 	mov    %rax,0x120(%r15,%r12,1)
    31ef:	e9 d6 f5 ff ff       	jmp    27ca <main+0x26a>
    31f4:	e8 17 f1 ff ff       	call   2310 <__stack_chk_fail@plt>
    31f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003200 <_start>:
    3200:	f3 0f 1e fa          	endbr64
    3204:	31 ed                	xor    %ebp,%ebp
    3206:	49 89 d1             	mov    %rdx,%r9
    3209:	5e                   	pop    %rsi
    320a:	48 89 e2             	mov    %rsp,%rdx
    320d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    3211:	50                   	push   %rax
    3212:	54                   	push   %rsp
    3213:	45 31 c0             	xor    %r8d,%r8d
    3216:	31 c9                	xor    %ecx,%ecx
    3218:	48 8d 3d 41 f3 ff ff 	lea    -0xcbf(%rip),%rdi        # 2560 <main>
    321f:	ff 15 b3 5d 00 00    	call   *0x5db3(%rip)        # 8fd8 <__libc_start_main@GLIBC_2.34>
    3225:	f4                   	hlt
    3226:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003230 <deregister_tm_clones>:
    3230:	48 8d 3d e9 5d 00 00 	lea    0x5de9(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    3237:	48 8d 05 e2 5d 00 00 	lea    0x5de2(%rip),%rax        # 9020 <stderr@GLIBC_2.2.5>
    323e:	48 39 f8             	cmp    %rdi,%rax
    3241:	74 15                	je     3258 <deregister_tm_clones+0x28>
    3243:	48 8b 05 96 5d 00 00 	mov    0x5d96(%rip),%rax        # 8fe0 <_ITM_deregisterTMCloneTable@Base>
    324a:	48 85 c0             	test   %rax,%rax
    324d:	74 09                	je     3258 <deregister_tm_clones+0x28>
    324f:	ff e0                	jmp    *%rax
    3251:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3258:	c3                   	ret
    3259:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003260 <register_tm_clones>:
    3260:	48 8d 3d b9 5d 00 00 	lea    0x5db9(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    3267:	48 8d 35 b2 5d 00 00 	lea    0x5db2(%rip),%rsi        # 9020 <stderr@GLIBC_2.2.5>
    326e:	48 29 fe             	sub    %rdi,%rsi
    3271:	48 89 f0             	mov    %rsi,%rax
    3274:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3278:	48 c1 f8 03          	sar    $0x3,%rax
    327c:	48 01 c6             	add    %rax,%rsi
    327f:	48 d1 fe             	sar    %rsi
    3282:	74 14                	je     3298 <register_tm_clones+0x38>
    3284:	48 8b 05 65 5d 00 00 	mov    0x5d65(%rip),%rax        # 8ff0 <_ITM_registerTMCloneTable@Base>
    328b:	48 85 c0             	test   %rax,%rax
    328e:	74 08                	je     3298 <register_tm_clones+0x38>
    3290:	ff e0                	jmp    *%rax
    3292:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3298:	c3                   	ret
    3299:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000032a0 <__do_global_dtors_aux>:
    32a0:	f3 0f 1e fa          	endbr64
    32a4:	80 3d 7d 5d 00 00 00 	cmpb   $0x0,0x5d7d(%rip)        # 9028 <completed.0>
    32ab:	75 2b                	jne    32d8 <__do_global_dtors_aux+0x38>
    32ad:	55                   	push   %rbp
    32ae:	48 83 3d 42 5d 00 00 00 	cmpq   $0x0,0x5d42(%rip)        # 8ff8 <__cxa_finalize@GLIBC_2.2.5>
    32b6:	48 89 e5             	mov    %rsp,%rbp
    32b9:	74 0c                	je     32c7 <__do_global_dtors_aux+0x27>
    32bb:	48 8b 3d 46 5d 00 00 	mov    0x5d46(%rip),%rdi        # 9008 <__dso_handle>
    32c2:	e8 d9 ef ff ff       	call   22a0 <__cxa_finalize@plt>
    32c7:	e8 64 ff ff ff       	call   3230 <deregister_tm_clones>
    32cc:	c6 05 55 5d 00 00 01 	movb   $0x1,0x5d55(%rip)        # 9028 <completed.0>
    32d3:	5d                   	pop    %rbp
    32d4:	c3                   	ret
    32d5:	0f 1f 00             	nopl   (%rax)
    32d8:	c3                   	ret
    32d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000032e0 <frame_dummy>:
    32e0:	f3 0f 1e fa          	endbr64
    32e4:	e9 77 ff ff ff       	jmp    3260 <register_tm_clones>
    32e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000032f0 <do_protected_write>:
    32f0:	f3 0f 1e fa          	endbr64
    32f4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    32fb:	48 8b 40 30          	mov    0x30(%rax),%rax
    32ff:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
    3307:	48 8b 48 08          	mov    0x8(%rax),%rcx
    330b:	48 83 00 01          	addq   $0x1,(%rax)
    330f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3316:	48 85 c9             	test   %rcx,%rcx
    3319:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3320:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3324:	48 89 50 08          	mov    %rdx,0x8(%rax)
    3328:	31 c0                	xor    %eax,%eax
    332a:	c3                   	ret
    332b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003330 <barriered_reset>:
    3330:	f3 0f 1e fa          	endbr64
    3334:	48 63 8f 84 01 00 00 	movslq 0x184(%rdi),%rcx
    333b:	85 c9                	test   %ecx,%ecx
    333d:	7e 6c                	jle    33ab <barriered_reset+0x7b>
    333f:	48 63 87 30 01 00 00 	movslq 0x130(%rdi),%rax
    3346:	4c 8b 87 28 01 00 00 	mov    0x128(%rdi),%r8
    334d:	48 8d 0c 89          	lea    (%rcx,%rcx,4),%rcx
    3351:	48 c1 e1 07          	shl    $0x7,%rcx
    3355:	48 8d 3c c0          	lea    (%rax,%rax,8),%rdi
    3359:	49 8b 70 20          	mov    0x20(%r8),%rsi
    335d:	48 8d 04 78          	lea    (%rax,%rdi,2),%rax
    3361:	49 8b 78 10          	mov    0x10(%r8),%rdi
    3365:	48 8d 96 80 01 00 00 	lea    0x180(%rsi),%rdx
    336c:	48 8d 8c 0e 80 01 00 00 	lea    0x180(%rsi,%rcx,1),%rcx
    3374:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    3378:	48 8b 40 20          	mov    0x20(%rax),%rax
    337c:	48 05 00 01 00 00    	add    $0x100,%rax
    3382:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3388:	83 40 80 01          	addl   $0x1,-0x80(%rax)
    338c:	48 81 c2 80 02 00 00 	add    $0x280,%rdx
    3393:	83 00 01             	addl   $0x1,(%rax)
    3396:	48 05 80 02 00 00    	add    $0x280,%rax
    339c:	c7 82 80 fd ff ff 01 00 00 00 	movl   $0x1,-0x280(%rdx)
    33a6:	48 39 ca             	cmp    %rcx,%rdx
    33a9:	75 dd                	jne    3388 <barriered_reset+0x58>
    33ab:	0f ae f0             	mfence
    33ae:	31 c0                	xor    %eax,%eax
    33b0:	c3                   	ret
    33b1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    33bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000033c0 <barriered_thread>:
    33c0:	f3 0f 1e fa          	endbr64
    33c4:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
    33c8:	0f 85 d4 02 00 00    	jne    36a2 <barriered_thread+0x2e2>
    33ce:	41 57                	push   %r15
    33d0:	41 56                	push   %r14
    33d2:	45 31 f6             	xor    %r14d,%r14d
    33d5:	41 55                	push   %r13
    33d7:	45 31 ed             	xor    %r13d,%r13d
    33da:	41 54                	push   %r12
    33dc:	49 89 fc             	mov    %rdi,%r12
    33df:	55                   	push   %rbp
    33e0:	53                   	push   %rbx
    33e1:	31 db                	xor    %ebx,%ebx
    33e3:	48 83 ec 08          	sub    $0x8,%rsp
    33e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    33f0:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    33f5:	39 da                	cmp    %ebx,%edx
    33f7:	7f 13                	jg     340c <barriered_thread+0x4c>
    33f9:	49 83 84 24 90 00 00 00 01 	addq   $0x1,0x90(%r12)
    3402:	31 db                	xor    %ebx,%ebx
    3404:	85 d2                	test   %edx,%edx
    3406:	0f 8e 74 01 00 00    	jle    3580 <barriered_thread+0x1c0>
    340c:	48 63 c3             	movslq %ebx,%rax
    340f:	48 8d 2c 80          	lea    (%rax,%rax,4),%rbp
    3413:	48 c1 e5 07          	shl    $0x7,%rbp
    3417:	eb 19                	jmp    3432 <barriered_thread+0x72>
    3419:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3420:	83 c3 01             	add    $0x1,%ebx
    3423:	48 81 c5 80 02 00 00 	add    $0x280,%rbp
    342a:	39 d3                	cmp    %edx,%ebx
    342c:	0f 8d 4e 01 00 00    	jge    3580 <barriered_thread+0x1c0>
    3432:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    3437:	48 8d 0c 28          	lea    (%rax,%rbp,1),%rcx
    343b:	83 b9 80 01 00 00 01 	cmpl   $0x1,0x180(%rcx)
    3442:	75 dc                	jne    3420 <barriered_thread+0x60>
    3444:	41 8b 7c 24 18       	mov    0x18(%r12),%edi
    3449:	83 ea 01             	sub    $0x1,%edx
    344c:	8d 73 ff             	lea    -0x1(%rbx),%esi
    344f:	85 db                	test   %ebx,%ebx
    3451:	0f 4f d6             	cmovg  %esi,%edx
    3454:	85 ff                	test   %edi,%edi
    3456:	0f 8e 34 02 00 00    	jle    3690 <barriered_thread+0x2d0>
    345c:	48 63 d2             	movslq %edx,%rdx
    345f:	44 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9d
    3466:	45 31 d2             	xor    %r10d,%r10d
    3469:	45 31 ff             	xor    %r15d,%r15d
    346c:	48 8d 34 92          	lea    (%rdx,%rdx,4),%rsi
    3470:	48 63 d7             	movslq %edi,%rdx
    3473:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    347a:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    347f:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    3483:	48 c1 e6 07          	shl    $0x7,%rsi
    3487:	48 8d 14 4a          	lea    (%rdx,%rcx,2),%rdx
    348b:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    348f:	90                   	nop
    3490:	48 8b 50 20          	mov    0x20(%rax),%rdx
    3494:	48 01 f2             	add    %rsi,%rdx
    3497:	44 3b 8a 80 00 00 00 	cmp    0x80(%rdx),%r9d
    349e:	75 04                	jne    34a4 <barriered_thread+0xe4>
    34a0:	41 83 c7 01          	add    $0x1,%r15d
    34a4:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    34ab:	75 04                	jne    34b1 <barriered_thread+0xf1>
    34ad:	41 83 c2 01          	add    $0x1,%r10d
    34b1:	48 05 98 00 00 00    	add    $0x98,%rax
    34b7:	48 39 c8             	cmp    %rcx,%rax
    34ba:	75 d4                	jne    3490 <barriered_thread+0xd0>
    34bc:	44 39 d7             	cmp    %r10d,%edi
    34bf:	0f 84 db 00 00 00    	je     35a0 <barriered_thread+0x1e0>
    34c5:	45 85 d2             	test   %r10d,%r10d
    34c8:	0f 84 d2 00 00 00    	je     35a0 <barriered_thread+0x1e0>
    34ce:	45 85 ff             	test   %r15d,%r15d
    34d1:	74 0b                	je     34de <barriered_thread+0x11e>
    34d3:	45 39 7c 24 18       	cmp    %r15d,0x18(%r12)
    34d8:	0f 85 a2 00 00 00    	jne    3580 <barriered_thread+0x1c0>
    34de:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    34e3:	48 01 e8             	add    %rbp,%rax
    34e6:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
    34ed:	85 db                	test   %ebx,%ebx
    34ef:	75 10                	jne    3501 <barriered_thread+0x141>
    34f1:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
    34f6:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
    34fb:	0f 8c 67 01 00 00    	jl     3668 <barriered_thread+0x2a8>
    3501:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    350b:	49 63 14 24          	movslq (%r12),%rdx
    350f:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    3513:	48 8d 14 4a          	lea    (%rdx,%rcx,2),%rdx
    3517:	49 8b 4c 24 10       	mov    0x10(%r12),%rcx
    351c:	48 8d 14 d1          	lea    (%rcx,%rdx,8),%rdx
    3520:	48 8b 7a 20          	mov    0x20(%rdx),%rdi
    3524:	48 01 ef             	add    %rbp,%rdi
    3527:	ff 90 18 01 00 00    	call   *0x118(%rax)
    352d:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    3532:	48 01 e8             	add    %rbp,%rax
    3535:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
    353c:	41 8b 44 24 28       	mov    0x28(%r12),%eax
    3541:	49 83 44 24 60 01    	addq   $0x1,0x60(%r12)
    3547:	83 e8 01             	sub    $0x1,%eax
    354a:	39 d8                	cmp    %ebx,%eax
    354c:	0f 84 a6 00 00 00    	je     35f8 <barriered_thread+0x238>
    3552:	0f ae f0             	mfence
    3555:	45 85 f6             	test   %r14d,%r14d
    3558:	0f 84 d2 00 00 00    	je     3630 <barriered_thread+0x270>
    355e:	41 83 fe 03          	cmp    $0x3,%r14d
    3562:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    3567:	45 0f 44 f5          	cmove  %r13d,%r14d
    356b:	83 c3 01             	add    $0x1,%ebx
    356e:	48 81 c5 80 02 00 00 	add    $0x280,%rbp
    3575:	39 d3                	cmp    %edx,%ebx
    3577:	0f 8c b5 fe ff ff    	jl     3432 <barriered_thread+0x72>
    357d:	0f 1f 00             	nopl   (%rax)
    3580:	41 83 7c 24 2c 01    	cmpl   $0x1,0x2c(%r12)
    3586:	0f 84 64 fe ff ff    	je     33f0 <barriered_thread+0x30>
    358c:	48 83 c4 08          	add    $0x8,%rsp
    3590:	31 c0                	xor    %eax,%eax
    3592:	5b                   	pop    %rbx
    3593:	5d                   	pop    %rbp
    3594:	41 5c                	pop    %r12
    3596:	41 5d                	pop    %r13
    3598:	41 5e                	pop    %r14
    359a:	41 5f                	pop    %r15
    359c:	c3                   	ret
    359d:	0f 1f 00             	nopl   (%rax)
    35a0:	41 83 fe 01          	cmp    $0x1,%r14d
    35a4:	0f 85 24 ff ff ff    	jne    34ce <barriered_thread+0x10e>
    35aa:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    35b2:	bf 04 00 00 00       	mov    $0x4,%edi
    35b7:	41 be 03 00 00 00    	mov    $0x3,%r14d
    35bd:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    35c1:	49 8b 44 24 78       	mov    0x78(%r12),%rax
    35c6:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    35cb:	e8 20 ed ff ff       	call   22f0 <clock_gettime@plt>
    35d0:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    35d8:	48 83 c0 01          	add    $0x1,%rax
    35dc:	48 99                	cqto
    35de:	49 f7 bc 24 88 00 00 00 	idivq  0x88(%r12)
    35e6:	49 89 94 24 80 00 00 00 	mov    %rdx,0x80(%r12)
    35ee:	e9 db fe ff ff       	jmp    34ce <barriered_thread+0x10e>
    35f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    35f8:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
    35fd:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
    3602:	0f 8d 4a ff ff ff    	jge    3552 <barriered_thread+0x192>
    3608:	48 c1 e6 04          	shl    $0x4,%rsi
    360c:	bf 04 00 00 00       	mov    $0x4,%edi
    3611:	49 03 74 24 58       	add    0x58(%r12),%rsi
    3616:	e8 d5 ec ff ff       	call   22f0 <clock_gettime@plt>
    361b:	49 83 44 24 68 01    	addq   $0x1,0x68(%r12)
    3621:	e9 2c ff ff ff       	jmp    3552 <barriered_thread+0x192>
    3626:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3630:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    3638:	bf 04 00 00 00       	mov    $0x4,%edi
    363d:	41 be 01 00 00 00    	mov    $0x1,%r14d
    3643:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3647:	49 8b 44 24 78       	mov    0x78(%r12),%rax
    364c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3650:	89 5e 20             	mov    %ebx,0x20(%rsi)
    3653:	e8 98 ec ff ff       	call   22f0 <clock_gettime@plt>
    3658:	41 8b 54 24 28       	mov    0x28(%r12),%edx
    365d:	e9 be fd ff ff       	jmp    3420 <barriered_thread+0x60>
    3662:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3668:	48 c1 e6 04          	shl    $0x4,%rsi
    366c:	bf 04 00 00 00       	mov    $0x4,%edi
    3671:	49 03 74 24 50       	add    0x50(%r12),%rsi
    3676:	e8 75 ec ff ff       	call   22f0 <clock_gettime@plt>
    367b:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    3680:	48 01 e8             	add    %rbp,%rax
    3683:	e9 79 fe ff ff       	jmp    3501 <barriered_thread+0x141>
    3688:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3690:	41 83 fe 01          	cmp    $0x1,%r14d
    3694:	0f 85 49 fe ff ff    	jne    34e3 <barriered_thread+0x123>
    369a:	45 31 ff             	xor    %r15d,%r15d
    369d:	e9 08 ff ff ff       	jmp    35aa <barriered_thread+0x1ea>
    36a2:	31 c0                	xor    %eax,%eax
    36a4:	c3                   	ret
    36a5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000036b0 <external_thread>:
    36b0:	f3 0f 1e fa          	endbr64
    36b4:	41 55                	push   %r13
    36b6:	41 54                	push   %r12
    36b8:	55                   	push   %rbp
    36b9:	53                   	push   %rbx
    36ba:	48 83 ec 38          	sub    $0x38,%rsp
    36be:	66 0f 6f 05 2a 32 00 00 	movdqa 0x322a(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
    36c6:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    36cf:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    36d4:	31 c0                	xor    %eax,%eax
    36d6:	83 7f 2c 01          	cmpl   $0x1,0x2c(%rdi)
    36da:	0f 29 04 24          	movaps %xmm0,(%rsp)
    36de:	75 64                	jne    3744 <external_thread+0x94>
    36e0:	49 89 fd             	mov    %rdi,%r13
    36e3:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    36e8:	48 89 e3             	mov    %rsp,%rbx
    36eb:	4c 8d 25 12 29 00 00 	lea    0x2912(%rip),%r12        # 6004 <_IO_stdin_used+0x4>
    36f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    36f8:	48 89 ee             	mov    %rbp,%rsi
    36fb:	48 89 df             	mov    %rbx,%rdi
    36fe:	e8 2d ec ff ff       	call   2330 <nanosleep@plt>
    3703:	49 8b 45 38          	mov    0x38(%r13),%rax
    3707:	48 63 10             	movslq (%rax),%rdx
    370a:	85 d2                	test   %edx,%edx
    370c:	7e 2c                	jle    373a <external_thread+0x8a>
    370e:	48 8b 40 08          	mov    0x8(%rax),%rax
    3712:	48 c1 e2 04          	shl    $0x4,%rdx
    3716:	48 01 c2             	add    %rax,%rdx
    3719:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3720:	8b 48 08             	mov    0x8(%rax),%ecx
    3723:	85 c9                	test   %ecx,%ecx
    3725:	75 0a                	jne    3731 <external_thread+0x81>
    3727:	4c 89 20             	mov    %r12,(%rax)
    372a:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    3731:	48 83 c0 10          	add    $0x10,%rax
    3735:	48 39 c2             	cmp    %rax,%rdx
    3738:	75 e6                	jne    3720 <external_thread+0x70>
    373a:	0f ae f0             	mfence
    373d:	41 83 7d 2c 01       	cmpl   $0x1,0x2c(%r13)
    3742:	74 b4                	je     36f8 <external_thread+0x48>
    3744:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3749:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3752:	75 0d                	jne    3761 <external_thread+0xb1>
    3754:	48 83 c4 38          	add    $0x38,%rsp
    3758:	31 c0                	xor    %eax,%eax
    375a:	5b                   	pop    %rbx
    375b:	5d                   	pop    %rbp
    375c:	41 5c                	pop    %r12
    375e:	41 5d                	pop    %r13
    3760:	c3                   	ret
    3761:	e8 aa eb ff ff       	call   2310 <__stack_chk_fail@plt>
    3766:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000003770 <timer_thread>:
    3770:	f3 0f 1e fa          	endbr64
    3774:	41 57                	push   %r15
    3776:	48 8d 35 93 28 00 00 	lea    0x2893(%rip),%rsi        # 6010 <_IO_stdin_used+0x10>
    377d:	49 89 ff             	mov    %rdi,%r15
    3780:	41 56                	push   %r14
    3782:	41 55                	push   %r13
    3784:	41 54                	push   %r12
    3786:	55                   	push   %rbp
    3787:	53                   	push   %rbx
    3788:	48 83 ec 58          	sub    $0x58,%rsp
    378c:	8b 17                	mov    (%rdi),%edx
    378e:	bf 01 00 00 00       	mov    $0x1,%edi
    3793:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    379c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    37a1:	31 c0                	xor    %eax,%eax
    37a3:	e8 88 ec ff ff       	call   2430 <__printf_chk@plt>
    37a8:	66 0f 6f 05 40 31 00 00 	movdqa 0x3140(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
    37b0:	ba 30 75 00 00       	mov    $0x7530,%edx
    37b5:	31 c0                	xor    %eax,%eax
    37b7:	48 8d 35 64 28 00 00 	lea    0x2864(%rip),%rsi        # 6022 <_IO_stdin_used+0x22>
    37be:	bf 01 00 00 00       	mov    $0x1,%edi
    37c3:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    37c8:	e8 63 ec ff ff       	call   2430 <__printf_chk@plt>
    37cd:	4d 63 77 2c          	movslq 0x2c(%r15),%r14
    37d1:	45 85 f6             	test   %r14d,%r14d
    37d4:	0f 84 a3 00 00 00    	je     387d <timer_thread+0x10d>
    37da:	45 31 ed             	xor    %r13d,%r13d
    37dd:	45 31 f6             	xor    %r14d,%r14d
    37e0:	49 89 e4             	mov    %rsp,%r12
    37e3:	31 db                	xor    %ebx,%ebx
    37e5:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    37ea:	48 89 ef             	mov    %rbp,%rdi
    37ed:	4c 89 e6             	mov    %r12,%rsi
    37f0:	41 83 c5 01          	add    $0x1,%r13d
    37f4:	e8 37 eb ff ff       	call   2330 <nanosleep@plt>
    37f9:	49 63 47 18          	movslq 0x18(%r15),%rax
    37fd:	41 8d 7e 01          	lea    0x1(%r14),%edi
    3801:	85 c0                	test   %eax,%eax
    3803:	7e 53                	jle    3858 <timer_thread+0xe8>
    3805:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    3809:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    380d:	4f 8d 04 b6          	lea    (%r14,%r14,4),%r8
    3811:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    3815:	49 c1 e0 07          	shl    $0x7,%r8
    3819:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    381d:	0f 1f 00             	nopl   (%rax)
    3820:	89 f8                	mov    %edi,%eax
    3822:	48 8b 71 20          	mov    0x20(%rcx),%rsi
    3826:	99                   	cltd
    3827:	f7 79 28             	idivl  0x28(%rcx)
    382a:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3831:	48 63 d2             	movslq %edx,%rdx
    3834:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
    3838:	48 c1 e0 07          	shl    $0x7,%rax
    383c:	c7 84 06 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rsi,%rax,1)
    3847:	42 c7 84 06 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rsi,%r8,1)
    3853:	49 39 c9             	cmp    %rcx,%r9
    3856:	75 c8                	jne    3820 <timer_thread+0xb0>
    3858:	0f ae f0             	mfence
    385b:	49 8b 47 10          	mov    0x10(%r15),%rax
    385f:	41 8b 57 2c          	mov    0x2c(%r15),%edx
    3863:	39 78 28             	cmp    %edi,0x28(%rax)
    3866:	0f 4e fb             	cmovle %ebx,%edi
    3869:	4c 63 f7             	movslq %edi,%r14
    386c:	85 d2                	test   %edx,%edx
    386e:	74 0d                	je     387d <timer_thread+0x10d>
    3870:	41 81 fd 30 75 00 00 	cmp    $0x7530,%r13d
    3877:	0f 85 6d ff ff ff    	jne    37ea <timer_thread+0x7a>
    387d:	48 8d 3d b4 27 00 00 	lea    0x27b4(%rip),%rdi        # 6038 <_IO_stdin_used+0x38>
    3884:	e8 47 ea ff ff       	call   22d0 <puts@plt>
    3889:	49 63 47 1c          	movslq 0x1c(%r15),%rax
    388d:	85 c0                	test   %eax,%eax
    388f:	7e 5c                	jle    38ed <timer_thread+0x17d>
    3891:	41 8b 57 28          	mov    0x28(%r15),%edx
    3895:	85 d2                	test   %edx,%edx
    3897:	7e 54                	jle    38ed <timer_thread+0x17d>
    3899:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    389d:	4d 8b 47 10          	mov    0x10(%r15),%r8
    38a1:	48 8d 34 48          	lea    (%rax,%rcx,2),%rsi
    38a5:	48 63 c2             	movslq %edx,%rax
    38a8:	31 c9                	xor    %ecx,%ecx
    38aa:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    38ae:	48 c1 e6 03          	shl    $0x3,%rsi
    38b2:	48 c1 e0 07          	shl    $0x7,%rax
    38b6:	48 8d b8 38 02 00 00 	lea    0x238(%rax),%rdi
    38bd:	49 8b 54 08 20       	mov    0x20(%r8,%rcx,1),%rdx
    38c2:	48 8d 82 38 02 00 00 	lea    0x238(%rdx),%rax
    38c9:	48 01 fa             	add    %rdi,%rdx
    38cc:	0f 1f 40 00          	nopl   0x0(%rax)
    38d0:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    38d6:	48 05 80 02 00 00    	add    $0x280,%rax
    38dc:	48 39 d0             	cmp    %rdx,%rax
    38df:	75 ef                	jne    38d0 <timer_thread+0x160>
    38e1:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    38e8:	48 39 f1             	cmp    %rsi,%rcx
    38eb:	75 d0                	jne    38bd <timer_thread+0x14d>
    38ed:	0f ae f0             	mfence
    38f0:	66 0f 6f 05 08 30 00 00 	movdqa 0x3008(%rip),%xmm0        # 6900 <_IO_stdin_used+0x900>
    38f8:	48 8d 2d 5e 27 00 00 	lea    0x275e(%rip),%rbp        # 605d <_IO_stdin_used+0x5d>
    38ff:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    3904:	49 63 47 18          	movslq 0x18(%r15),%rax
    3908:	45 8d 6e 01          	lea    0x1(%r14),%r13d
    390c:	85 c0                	test   %eax,%eax
    390e:	7e 58                	jle    3968 <timer_thread+0x1f8>
    3910:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    3914:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3918:	4b 8d 3c b6          	lea    (%r14,%r14,4),%rdi
    391c:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    3920:	48 c1 e7 07          	shl    $0x7,%rdi
    3924:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    3928:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3930:	44 89 e8             	mov    %r13d,%eax
    3933:	48 8b 71 20          	mov    0x20(%rcx),%rsi
    3937:	99                   	cltd
    3938:	f7 79 28             	idivl  0x28(%rcx)
    393b:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3942:	48 63 c2             	movslq %edx,%rax
    3945:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3949:	48 c1 e0 07          	shl    $0x7,%rax
    394d:	c7 84 06 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rsi,%rax,1)
    3958:	c7 84 3e 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rsi,%rdi,1)
    3963:	4c 39 c1             	cmp    %r8,%rcx
    3966:	75 c8                	jne    3930 <timer_thread+0x1c0>
    3968:	0f ae f0             	mfence
    396b:	49 8b 47 10          	mov    0x10(%r15),%rax
    396f:	44 39 68 28          	cmp    %r13d,0x28(%rax)
    3973:	7f 03                	jg     3978 <timer_thread+0x208>
    3975:	45 31 ed             	xor    %r13d,%r13d
    3978:	41 8b 7f 18          	mov    0x18(%r15),%edi
    397c:	85 ff                	test   %edi,%edi
    397e:	0f 8e b7 00 00 00    	jle    3a3b <timer_thread+0x2cb>
    3984:	45 31 e4             	xor    %r12d,%r12d
    3987:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    398d:	31 db                	xor    %ebx,%ebx
    398f:	90                   	nop
    3990:	45 31 f6             	xor    %r14d,%r14d
    3993:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3998:	85 ff                	test   %edi,%edi
    399a:	7e 64                	jle    3a00 <timer_thread+0x290>
    399c:	49 8b 57 10          	mov    0x10(%r15),%rdx
    39a0:	4b 8d 04 b6          	lea    (%r14,%r14,4),%rax
    39a4:	48 c1 e0 07          	shl    $0x7,%rax
    39a8:	48 03 44 1a 20       	add    0x20(%rdx,%rbx,1),%rax
    39ad:	31 d2                	xor    %edx,%edx
    39af:	48 8b 80 28 02 00 00 	mov    0x228(%rax),%rax
    39b6:	eb 18                	jmp    39d0 <timer_thread+0x260>
    39b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    39c0:	4d 85 c0             	test   %r8,%r8
    39c3:	7f 25                	jg     39ea <timer_thread+0x27a>
    39c5:	83 c2 01             	add    $0x1,%edx
    39c8:	48 83 c0 20          	add    $0x20,%rax
    39cc:	39 fa                	cmp    %edi,%edx
    39ce:	74 30                	je     3a00 <timer_thread+0x290>
    39d0:	48 8b 08             	mov    (%rax),%rcx
    39d3:	48 8b 70 08          	mov    0x8(%rax),%rsi
    39d7:	48 8b 89 80 00 00 00 	mov    0x80(%rcx),%rcx
    39de:	4c 8b 86 80 00 00 00 	mov    0x80(%rsi),%r8
    39e5:	48 85 c9             	test   %rcx,%rcx
    39e8:	7e d6                	jle    39c0 <timer_thread+0x250>
    39ea:	bf 01 00 00 00       	mov    $0x1,%edi
    39ef:	48 89 ee             	mov    %rbp,%rsi
    39f2:	31 c0                	xor    %eax,%eax
    39f4:	e8 37 ea ff ff       	call   2430 <__printf_chk@plt>
    39f9:	41 8b 7f 18          	mov    0x18(%r15),%edi
    39fd:	45 31 c9             	xor    %r9d,%r9d
    3a00:	49 83 c6 01          	add    $0x1,%r14
    3a04:	44 39 f7             	cmp    %r14d,%edi
    3a07:	7f 8f                	jg     3998 <timer_thread+0x228>
    3a09:	41 83 c4 01          	add    $0x1,%r12d
    3a0d:	41 39 fc             	cmp    %edi,%r12d
    3a10:	7d 0c                	jge    3a1e <timer_thread+0x2ae>
    3a12:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3a19:	e9 72 ff ff ff       	jmp    3990 <timer_thread+0x220>
    3a1e:	41 83 f9 01          	cmp    $0x1,%r9d
    3a22:	74 17                	je     3a3b <timer_thread+0x2cb>
    3a24:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3a29:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3a2e:	4d 63 f5             	movslq %r13d,%r14
    3a31:	e8 fa e8 ff ff       	call   2330 <nanosleep@plt>
    3a36:	e9 c9 fe ff ff       	jmp    3904 <timer_thread+0x194>
    3a3b:	48 8d 3d 12 26 00 00 	lea    0x2612(%rip),%rdi        # 6054 <_IO_stdin_used+0x54>
    3a42:	e8 89 e8 ff ff       	call   22d0 <puts@plt>
    3a47:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    3a4b:	85 c0                	test   %eax,%eax
    3a4d:	0f 84 c1 00 00 00    	je     3b14 <timer_thread+0x3a4>
    3a53:	41 8b 57 1c          	mov    0x1c(%r15),%edx
    3a57:	85 d2                	test   %edx,%edx
    3a59:	7e 38                	jle    3a93 <timer_thread+0x323>
    3a5b:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    3a5f:	31 db                	xor    %ebx,%ebx
    3a61:	31 ed                	xor    %ebp,%ebp
    3a63:	4c 8d 25 04 26 00 00 	lea    0x2604(%rip),%r12        # 606e <_IO_stdin_used+0x6e>
    3a6a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3a70:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    3a74:	83 78 04 02          	cmpl   $0x2,0x4(%rax)
    3a78:	c7 40 2c 00 00 00 00 	movl   $0x0,0x2c(%rax)
    3a7f:	0f 84 bc 00 00 00    	je     3b41 <timer_thread+0x3d1>
    3a85:	83 c5 01             	add    $0x1,%ebp
    3a88:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3a8f:	39 d5                	cmp    %edx,%ebp
    3a91:	7c dd                	jl     3a70 <timer_thread+0x300>
    3a93:	49 63 47 18          	movslq 0x18(%r15),%rax
    3a97:	85 c0                	test   %eax,%eax
    3a99:	7e 62                	jle    3afd <timer_thread+0x38d>
    3a9b:	41 8b 57 28          	mov    0x28(%r15),%edx
    3a9f:	85 d2                	test   %edx,%edx
    3aa1:	7e 5a                	jle    3afd <timer_thread+0x38d>
    3aa3:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    3aa7:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3aab:	48 8d 34 48          	lea    (%rax,%rcx,2),%rsi
    3aaf:	48 63 c2             	movslq %edx,%rax
    3ab2:	31 c9                	xor    %ecx,%ecx
    3ab4:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    3ab8:	48 c1 e6 03          	shl    $0x3,%rsi
    3abc:	48 c1 e0 07          	shl    $0x7,%rax
    3ac0:	48 8d b8 00 02 00 00 	lea    0x200(%rax),%rdi
    3ac7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3ad0:	49 8b 54 08 20       	mov    0x20(%r8,%rcx,1),%rdx
    3ad5:	48 8d 82 00 02 00 00 	lea    0x200(%rdx),%rax
    3adc:	48 01 fa             	add    %rdi,%rdx
    3adf:	90                   	nop
    3ae0:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    3ae6:	48 05 80 02 00 00    	add    $0x280,%rax
    3aec:	48 39 c2             	cmp    %rax,%rdx
    3aef:	75 ef                	jne    3ae0 <timer_thread+0x370>
    3af1:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3af8:	48 39 ce             	cmp    %rcx,%rsi
    3afb:	75 d3                	jne    3ad0 <timer_thread+0x360>
    3afd:	0f ae f0             	mfence
    3b00:	48 8d 3d 79 25 00 00 	lea    0x2579(%rip),%rdi        # 6080 <_IO_stdin_used+0x80>
    3b07:	e8 c4 e7 ff ff       	call   22d0 <puts@plt>
    3b0c:	41 c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%r15)
    3b14:	48 8d 3d 6c 25 00 00 	lea    0x256c(%rip),%rdi        # 6087 <_IO_stdin_used+0x87>
    3b1b:	e8 b0 e7 ff ff       	call   22d0 <puts@plt>
    3b20:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3b25:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3b2e:	75 4a                	jne    3b7a <timer_thread+0x40a>
    3b30:	48 83 c4 58          	add    $0x58,%rsp
    3b34:	31 c0                	xor    %eax,%eax
    3b36:	5b                   	pop    %rbx
    3b37:	5d                   	pop    %rbp
    3b38:	41 5c                	pop    %r12
    3b3a:	41 5d                	pop    %r13
    3b3c:	41 5e                	pop    %r14
    3b3e:	41 5f                	pop    %r15
    3b40:	c3                   	ret
    3b41:	4c 89 e7             	mov    %r12,%rdi
    3b44:	83 c5 01             	add    $0x1,%ebp
    3b47:	e8 84 e7 ff ff       	call   22d0 <puts@plt>
    3b4c:	49 8b 47 10          	mov    0x10(%r15),%rax
    3b50:	be 01 00 00 00       	mov    $0x1,%esi
    3b55:	8b 7c 18 48          	mov    0x48(%rax,%rbx,1),%edi
    3b59:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    3b60:	e8 7b e8 ff ff       	call   23e0 <eventfd_write@plt>
    3b65:	41 8b 57 1c          	mov    0x1c(%r15),%edx
    3b69:	39 d5                	cmp    %edx,%ebp
    3b6b:	0f 8d 22 ff ff ff    	jge    3a93 <timer_thread+0x323>
    3b71:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    3b75:	e9 f6 fe ff ff       	jmp    3a70 <timer_thread+0x300>
    3b7a:	e8 91 e7 ff ff       	call   2310 <__stack_chk_fail@plt>
    3b7f:	90                   	nop

0000000000003b80 <fatal_error>:
    3b80:	f3 0f 1e fa          	endbr64
    3b84:	50                   	push   %rax
    3b85:	58                   	pop    %rax
    3b86:	48 83 ec 08          	sub    $0x8,%rsp
    3b8a:	e8 e1 e8 ff ff       	call   2470 <perror@plt>
    3b8f:	bf 01 00 00 00       	mov    $0x1,%edi
    3b94:	e8 e7 e8 ff ff       	call   2480 <exit@plt>
    3b99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003ba0 <strtolower>:
    3ba0:	f3 0f 1e fa          	endbr64
    3ba4:	55                   	push   %rbp
    3ba5:	53                   	push   %rbx
    3ba6:	48 83 ec 08          	sub    $0x8,%rsp
    3baa:	48 0f be 1f          	movsbq (%rdi),%rbx
    3bae:	84 db                	test   %bl,%bl
    3bb0:	74 24                	je     3bd6 <strtolower+0x36>
    3bb2:	48 89 fd             	mov    %rdi,%rbp
    3bb5:	e8 36 e9 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3bba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3bc0:	48 8b 10             	mov    (%rax),%rdx
    3bc3:	48 83 c5 01          	add    $0x1,%rbp
    3bc7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3bca:	88 55 ff             	mov    %dl,-0x1(%rbp)
    3bcd:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3bd2:	84 db                	test   %bl,%bl
    3bd4:	75 ea                	jne    3bc0 <strtolower+0x20>
    3bd6:	48 83 c4 08          	add    $0x8,%rsp
    3bda:	5b                   	pop    %rbx
    3bdb:	5d                   	pop    %rbp
    3bdc:	c3                   	ret
    3bdd:	0f 1f 00             	nopl   (%rax)

0000000000003be0 <zh_malloc>:
    3be0:	f3 0f 1e fa          	endbr64
    3be4:	48 83 ec 08          	sub    $0x8,%rsp
    3be8:	e8 03 e8 ff ff       	call   23f0 <malloc@plt>
    3bed:	48 85 c0             	test   %rax,%rax
    3bf0:	74 05                	je     3bf7 <zh_malloc+0x17>
    3bf2:	48 83 c4 08          	add    $0x8,%rsp
    3bf6:	c3                   	ret
    3bf7:	48 8b 0d 22 54 00 00 	mov    0x5422(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    3bfe:	ba 28 00 00 00       	mov    $0x28,%edx
    3c03:	be 01 00 00 00       	mov    $0x1,%esi
    3c08:	48 8d 3d 11 28 00 00 	lea    0x2811(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    3c0f:	e8 8c e8 ff ff       	call   24a0 <fwrite@plt>
    3c14:	bf 01 00 00 00       	mov    $0x1,%edi
    3c19:	e8 62 e8 ff ff       	call   2480 <exit@plt>
    3c1e:	66 90                	xchg   %ax,%ax

0000000000003c20 <get_filename_ext>:
    3c20:	f3 0f 1e fa          	endbr64
    3c24:	53                   	push   %rbx
    3c25:	be 2e 00 00 00       	mov    $0x2e,%esi
    3c2a:	48 89 fb             	mov    %rdi,%rbx
    3c2d:	e8 0e e7 ff ff       	call   2340 <strrchr@plt>
    3c32:	48 85 c0             	test   %rax,%rax
    3c35:	74 11                	je     3c48 <get_filename_ext+0x28>
    3c37:	48 39 c3             	cmp    %rax,%rbx
    3c3a:	74 0c                	je     3c48 <get_filename_ext+0x28>
    3c3c:	48 83 c0 01          	add    $0x1,%rax
    3c40:	5b                   	pop    %rbx
    3c41:	c3                   	ret
    3c42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3c48:	48 8d 05 80 24 00 00 	lea    0x2480(%rip),%rax        # 60cf <_IO_stdin_used+0xcf>
    3c4f:	5b                   	pop    %rbx
    3c50:	c3                   	ret
    3c51:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3c5c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003c60 <send_headers>:
    3c60:	f3 0f 1e fa          	endbr64
    3c64:	41 55                	push   %r13
    3c66:	49 89 f5             	mov    %rsi,%r13
    3c69:	48 89 fe             	mov    %rdi,%rsi
    3c6c:	41 54                	push   %r12
    3c6e:	55                   	push   %rbp
    3c6f:	48 89 d5             	mov    %rdx,%rbp
    3c72:	ba 00 04 00 00       	mov    $0x400,%edx
    3c77:	53                   	push   %rbx
    3c78:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    3c7f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3c88:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3c90:	31 c0                	xor    %eax,%eax
    3c92:	49 89 e4             	mov    %rsp,%r12
    3c95:	4c 89 e7             	mov    %r12,%rdi
    3c98:	e8 73 e7 ff ff       	call   2410 <__strcpy_chk@plt>
    3c9d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3ca2:	84 db                	test   %bl,%bl
    3ca4:	74 24                	je     3cca <send_headers+0x6a>
    3ca6:	e8 45 e8 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3cab:	48 8b 08             	mov    (%rax),%rcx
    3cae:	4c 89 e0             	mov    %r12,%rax
    3cb1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3cb8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    3cbb:	48 83 c0 01          	add    $0x1,%rax
    3cbf:	88 50 ff             	mov    %dl,-0x1(%rax)
    3cc2:	48 0f be 18          	movsbq (%rax),%rbx
    3cc6:	84 db                	test   %bl,%bl
    3cc8:	75 ee                	jne    3cb8 <send_headers+0x58>
    3cca:	bf 11 00 00 00       	mov    $0x11,%edi
    3ccf:	e8 1c e7 ff ff       	call   23f0 <malloc@plt>
    3cd4:	48 85 c0             	test   %rax,%rax
    3cd7:	0f 84 7e 04 00 00    	je     415b <send_headers+0x4fb>
    3cdd:	66 0f 6f 05 2b 2c 00 00 	movdqa 0x2c2b(%rip),%xmm0        # 6910 <_IO_stdin_used+0x910>
    3ce5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    3ce9:	bf 17 00 00 00       	mov    $0x17,%edi
    3cee:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3cf6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3cfa:	0f 11 00             	movups %xmm0,(%rax)
    3cfd:	e8 ee e6 ff ff       	call   23f0 <malloc@plt>
    3d02:	48 85 c0             	test   %rax,%rax
    3d05:	0f 84 50 04 00 00    	je     415b <send_headers+0x4fb>
    3d0b:	66 0f 6f 05 0d 2c 00 00 	movdqa 0x2c0d(%rip),%xmm0        # 6920 <_IO_stdin_used+0x920>
    3d13:	48 89 45 10          	mov    %rax,0x10(%rbp)
    3d17:	4c 89 e7             	mov    %r12,%rdi
    3d1a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    3d24:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    3d2c:	0f 11 00             	movups %xmm0,(%rax)
    3d2f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    3d33:	be 2e 00 00 00       	mov    $0x2e,%esi
    3d38:	e8 03 e6 ff ff       	call   2340 <strrchr@plt>
    3d3d:	48 85 c0             	test   %rax,%rax
    3d40:	0f 84 ea 02 00 00    	je     4030 <send_headers+0x3d0>
    3d46:	4c 39 e0             	cmp    %r12,%rax
    3d49:	0f 84 e1 02 00 00    	je     4030 <send_headers+0x3d0>
    3d4f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    3d53:	48 8d 3d 43 23 00 00 	lea    0x2343(%rip),%rdi        # 609d <_IO_stdin_used+0x9d>
    3d5a:	48 89 de             	mov    %rbx,%rsi
    3d5d:	e8 2e e6 ff ff       	call   2390 <strcmp@plt>
    3d62:	85 c0                	test   %eax,%eax
    3d64:	75 20                	jne    3d86 <send_headers+0x126>
    3d66:	66 0f 6f 05 c2 2b 00 00 	movdqa 0x2bc2(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3d6e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3d76:	66 0f 6f 05 c2 2b 00 00 	movdqa 0x2bc2(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3d7e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    3d86:	48 89 de             	mov    %rbx,%rsi
    3d89:	48 8d 3d 11 23 00 00 	lea    0x2311(%rip),%rdi        # 60a1 <_IO_stdin_used+0xa1>
    3d90:	e8 fb e5 ff ff       	call   2390 <strcmp@plt>
    3d95:	85 c0                	test   %eax,%eax
    3d97:	75 20                	jne    3db9 <send_headers+0x159>
    3d99:	66 0f 6f 05 8f 2b 00 00 	movdqa 0x2b8f(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3da1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3da9:	66 0f 6f 05 8f 2b 00 00 	movdqa 0x2b8f(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3db1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    3db9:	48 89 de             	mov    %rbx,%rsi
    3dbc:	48 8d 3d e3 22 00 00 	lea    0x22e3(%rip),%rdi        # 60a6 <_IO_stdin_used+0xa6>
    3dc3:	e8 c8 e5 ff ff       	call   2390 <strcmp@plt>
    3dc8:	85 c0                	test   %eax,%eax
    3dca:	0f 84 10 02 00 00    	je     3fe0 <send_headers+0x380>
    3dd0:	48 89 de             	mov    %rbx,%rsi
    3dd3:	48 8d 3d d0 22 00 00 	lea    0x22d0(%rip),%rdi        # 60aa <_IO_stdin_used+0xaa>
    3dda:	e8 b1 e5 ff ff       	call   2390 <strcmp@plt>
    3ddf:	85 c0                	test   %eax,%eax
    3de1:	0f 84 a9 02 00 00    	je     4090 <send_headers+0x430>
    3de7:	48 89 de             	mov    %rbx,%rsi
    3dea:	48 8d 3d bd 22 00 00 	lea    0x22bd(%rip),%rdi        # 60ae <_IO_stdin_used+0xae>
    3df1:	e8 9a e5 ff ff       	call   2390 <strcmp@plt>
    3df6:	85 c0                	test   %eax,%eax
    3df8:	0f 84 6a 02 00 00    	je     4068 <send_headers+0x408>
    3dfe:	48 89 de             	mov    %rbx,%rsi
    3e01:	48 8d 3d e9 22 00 00 	lea    0x22e9(%rip),%rdi        # 60f1 <_IO_stdin_used+0xf1>
    3e08:	e8 83 e5 ff ff       	call   2390 <strcmp@plt>
    3e0d:	85 c0                	test   %eax,%eax
    3e0f:	0f 84 2b 02 00 00    	je     4040 <send_headers+0x3e0>
    3e15:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3e18:	0f 84 52 01 00 00    	je     3f70 <send_headers+0x310>
    3e1e:	48 89 de             	mov    %rbx,%rsi
    3e21:	48 8d 3d 8a 22 00 00 	lea    0x228a(%rip),%rdi        # 60b2 <_IO_stdin_used+0xb2>
    3e28:	e8 63 e5 ff ff       	call   2390 <strcmp@plt>
    3e2d:	85 c0                	test   %eax,%eax
    3e2f:	0f 84 ab 02 00 00    	je     40e0 <send_headers+0x480>
    3e35:	48 89 de             	mov    %rbx,%rsi
    3e38:	48 8d 3d 77 22 00 00 	lea    0x2277(%rip),%rdi        # 60b6 <_IO_stdin_used+0xb6>
    3e3f:	e8 4c e5 ff ff       	call   2390 <strcmp@plt>
    3e44:	85 c0                	test   %eax,%eax
    3e46:	0f 84 6c 02 00 00    	je     40b8 <send_headers+0x458>
    3e4c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    3e54:	4c 89 e7             	mov    %r12,%rdi
    3e57:	e8 a4 e4 ff ff       	call   2300 <strlen@plt>
    3e5c:	48 89 c7             	mov    %rax,%rdi
    3e5f:	48 89 c3             	mov    %rax,%rbx
    3e62:	e8 89 e5 ff ff       	call   23f0 <malloc@plt>
    3e67:	48 85 c0             	test   %rax,%rax
    3e6a:	0f 84 eb 02 00 00    	je     415b <send_headers+0x4fb>
    3e70:	48 89 45 20          	mov    %rax,0x20(%rbp)
    3e74:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
    3e78:	83 fb 08             	cmp    $0x8,%ebx
    3e7b:	0f 83 3f 01 00 00    	jae    3fc0 <send_headers+0x360>
    3e81:	f6 c3 04             	test   $0x4,%bl
    3e84:	0f 85 7b 02 00 00    	jne    4105 <send_headers+0x4a5>
    3e8a:	85 db                	test   %ebx,%ebx
    3e8c:	74 13                	je     3ea1 <send_headers+0x241>
    3e8e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3e96:	88 10                	mov    %dl,(%rax)
    3e98:	f6 c3 02             	test   $0x2,%bl
    3e9b:	0f 85 96 02 00 00    	jne    4137 <send_headers+0x4d7>
    3ea1:	4d 89 e8             	mov    %r13,%r8
    3ea4:	48 8d 0d 0f 22 00 00 	lea    0x220f(%rip),%rcx        # 60ba <_IO_stdin_used+0xba>
    3eab:	4c 89 e7             	mov    %r12,%rdi
    3eae:	31 c0                	xor    %eax,%eax
    3eb0:	ba 00 04 00 00       	mov    $0x400,%edx
    3eb5:	be 01 00 00 00       	mov    $0x1,%esi
    3eba:	e8 41 e6 ff ff       	call   2500 <__sprintf_chk@plt>
    3ebf:	4c 89 e7             	mov    %r12,%rdi
    3ec2:	e8 39 e4 ff ff       	call   2300 <strlen@plt>
    3ec7:	48 89 c7             	mov    %rax,%rdi
    3eca:	48 89 c3             	mov    %rax,%rbx
    3ecd:	e8 1e e5 ff ff       	call   23f0 <malloc@plt>
    3ed2:	48 85 c0             	test   %rax,%rax
    3ed5:	0f 84 80 02 00 00    	je     415b <send_headers+0x4fb>
    3edb:	48 89 45 30          	mov    %rax,0x30(%rbp)
    3edf:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    3ee3:	83 fb 08             	cmp    $0x8,%ebx
    3ee6:	0f 83 1c 01 00 00    	jae    4008 <send_headers+0x3a8>
    3eec:	f6 c3 04             	test   $0x4,%bl
    3eef:	0f 85 29 02 00 00    	jne    411e <send_headers+0x4be>
    3ef5:	85 db                	test   %ebx,%ebx
    3ef7:	74 13                	je     3f0c <send_headers+0x2ac>
    3ef9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3f01:	88 10                	mov    %dl,(%rax)
    3f03:	f6 c3 02             	test   $0x2,%bl
    3f06:	0f 85 3d 02 00 00    	jne    4149 <send_headers+0x4e9>
    3f0c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    3f11:	bf 02 00 00 00       	mov    $0x2,%edi
    3f16:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    3f1e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    3f26:	e8 c5 e4 ff ff       	call   23f0 <malloc@plt>
    3f2b:	48 85 c0             	test   %rax,%rax
    3f2e:	0f 84 27 02 00 00    	je     415b <send_headers+0x4fb>
    3f34:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    3f3c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    3f40:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    3f48:	66 89 10             	mov    %dx,(%rax)
    3f4b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    3f53:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3f5c:	0f 85 20 02 00 00    	jne    4182 <send_headers+0x522>
    3f62:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    3f69:	5b                   	pop    %rbx
    3f6a:	5d                   	pop    %rbp
    3f6b:	41 5c                	pop    %r12
    3f6d:	41 5d                	pop    %r13
    3f6f:	c3                   	ret
    3f70:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    3f74:	0f 85 a4 fe ff ff    	jne    3e1e <send_headers+0x1be>
    3f7a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    3f7e:	0f 85 9a fe ff ff    	jne    3e1e <send_headers+0x1be>
    3f84:	66 0f 6f 05 04 2a 00 00 	movdqa 0x2a04(%rip),%xmm0        # 6990 <_IO_stdin_used+0x990>
    3f8c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    3f96:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3f9e:	66 0f 6f 05 fa 29 00 00 	movdqa 0x29fa(%rip),%xmm0        # 69a0 <_IO_stdin_used+0x9a0>
    3fa6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    3fae:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    3fb6:	e9 63 fe ff ff       	jmp    3e1e <send_headers+0x1be>
    3fbb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3fc0:	89 da                	mov    %ebx,%edx
    3fc2:	48 89 c7             	mov    %rax,%rdi
    3fc5:	4c 89 e6             	mov    %r12,%rsi
    3fc8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    3fcd:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    3fd2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    3fd5:	c1 e9 03             	shr    $0x3,%ecx
    3fd8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    3fdb:	e9 c1 fe ff ff       	jmp    3ea1 <send_headers+0x241>
    3fe0:	66 0f 6f 05 48 29 00 00 	movdqa 0x2948(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3fe8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3ff0:	66 0f 6f 05 58 29 00 00 	movdqa 0x2958(%rip),%xmm0        # 6950 <_IO_stdin_used+0x950>
    3ff8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4000:	e9 cb fd ff ff       	jmp    3dd0 <send_headers+0x170>
    4005:	0f 1f 00             	nopl   (%rax)
    4008:	89 da                	mov    %ebx,%edx
    400a:	48 89 c7             	mov    %rax,%rdi
    400d:	4c 89 e6             	mov    %r12,%rsi
    4010:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4015:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    401a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    401d:	c1 e9 03             	shr    $0x3,%ecx
    4020:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4023:	e9 e4 fe ff ff       	jmp    3f0c <send_headers+0x2ac>
    4028:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4030:	48 8d 1d 98 20 00 00 	lea    0x2098(%rip),%rbx        # 60cf <_IO_stdin_used+0xcf>
    4037:	e9 94 fd ff ff       	jmp    3dd0 <send_headers+0x170>
    403c:	0f 1f 40 00          	nopl   0x0(%rax)
    4040:	66 0f 6f 05 28 29 00 00 	movdqa 0x2928(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4048:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4050:	66 0f 6f 05 28 29 00 00 	movdqa 0x2928(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    4058:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4060:	e9 b0 fd ff ff       	jmp    3e15 <send_headers+0x1b5>
    4065:	0f 1f 00             	nopl   (%rax)
    4068:	66 0f 6f 05 00 29 00 00 	movdqa 0x2900(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4070:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4078:	66 0f 6f 05 00 29 00 00 	movdqa 0x2900(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    4080:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4088:	e9 71 fd ff ff       	jmp    3dfe <send_headers+0x19e>
    408d:	0f 1f 00             	nopl   (%rax)
    4090:	66 0f 6f 05 98 28 00 00 	movdqa 0x2898(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    4098:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40a0:	66 0f 6f 05 b8 28 00 00 	movdqa 0x28b8(%rip),%xmm0        # 6960 <_IO_stdin_used+0x960>
    40a8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    40b0:	e9 32 fd ff ff       	jmp    3de7 <send_headers+0x187>
    40b5:	0f 1f 00             	nopl   (%rax)
    40b8:	66 0f 6f 05 b0 28 00 00 	movdqa 0x28b0(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    40c0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40c8:	66 0f 6f 05 f0 28 00 00 	movdqa 0x28f0(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    40d0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    40d8:	e9 6f fd ff ff       	jmp    3e4c <send_headers+0x1ec>
    40dd:	0f 1f 00             	nopl   (%rax)
    40e0:	66 0f 6f 05 88 28 00 00 	movdqa 0x2888(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    40e8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40f0:	66 0f 6f 05 b8 28 00 00 	movdqa 0x28b8(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    40f8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4100:	e9 30 fd ff ff       	jmp    3e35 <send_headers+0x1d5>
    4105:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    410c:	89 db                	mov    %ebx,%ebx
    410e:	89 10                	mov    %edx,(%rax)
    4110:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4115:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4119:	e9 83 fd ff ff       	jmp    3ea1 <send_headers+0x241>
    411e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4125:	89 db                	mov    %ebx,%ebx
    4127:	89 10                	mov    %edx,(%rax)
    4129:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    412e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4132:	e9 d5 fd ff ff       	jmp    3f0c <send_headers+0x2ac>
    4137:	89 db                	mov    %ebx,%ebx
    4139:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    413f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4144:	e9 58 fd ff ff       	jmp    3ea1 <send_headers+0x241>
    4149:	89 db                	mov    %ebx,%ebx
    414b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4151:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4156:	e9 b1 fd ff ff       	jmp    3f0c <send_headers+0x2ac>
    415b:	48 8b 0d be 4e 00 00 	mov    0x4ebe(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4162:	ba 28 00 00 00       	mov    $0x28,%edx
    4167:	be 01 00 00 00       	mov    $0x1,%esi
    416c:	48 8d 3d ad 22 00 00 	lea    0x22ad(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    4173:	e8 28 e3 ff ff       	call   24a0 <fwrite@plt>
    4178:	bf 01 00 00 00       	mov    $0x1,%edi
    417d:	e8 fe e2 ff ff       	call   2480 <exit@plt>
    4182:	e8 89 e1 ff ff       	call   2310 <__stack_chk_fail@plt>
    4187:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004190 <copy_file_contents>:
    4190:	f3 0f 1e fa          	endbr64
    4194:	41 55                	push   %r13
    4196:	49 89 d5             	mov    %rdx,%r13
    4199:	41 54                	push   %r12
    419b:	49 89 fc             	mov    %rdi,%r12
    419e:	48 89 f7             	mov    %rsi,%rdi
    41a1:	55                   	push   %rbp
    41a2:	53                   	push   %rbx
    41a3:	48 89 f3             	mov    %rsi,%rbx
    41a6:	48 83 ec 08          	sub    $0x8,%rsp
    41aa:	e8 41 e2 ff ff       	call   23f0 <malloc@plt>
    41af:	48 85 c0             	test   %rax,%rax
    41b2:	74 77                	je     422b <copy_file_contents+0x9b>
    41b4:	4c 89 e7             	mov    %r12,%rdi
    41b7:	48 89 c5             	mov    %rax,%rbp
    41ba:	31 f6                	xor    %esi,%esi
    41bc:	31 c0                	xor    %eax,%eax
    41be:	e8 9d e2 ff ff       	call   2460 <open@plt>
    41c3:	41 89 c4             	mov    %eax,%r12d
    41c6:	85 c0                	test   %eax,%eax
    41c8:	78 55                	js     421f <copy_file_contents+0x8f>
    41ca:	48 89 da             	mov    %rbx,%rdx
    41cd:	48 89 ee             	mov    %rbp,%rsi
    41d0:	89 c7                	mov    %eax,%edi
    41d2:	e8 99 e1 ff ff       	call   2370 <read@plt>
    41d7:	48 98                	cltq
    41d9:	48 39 d8             	cmp    %rbx,%rax
    41dc:	7c 22                	jl     4200 <copy_file_contents+0x70>
    41de:	44 89 e7             	mov    %r12d,%edi
    41e1:	e8 6a e1 ff ff       	call   2350 <close@plt>
    41e6:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    41ea:	49 89 5d 08          	mov    %rbx,0x8(%r13)
    41ee:	48 83 c4 08          	add    $0x8,%rsp
    41f2:	5b                   	pop    %rbx
    41f3:	5d                   	pop    %rbp
    41f4:	41 5c                	pop    %r12
    41f6:	41 5d                	pop    %r13
    41f8:	c3                   	ret
    41f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4200:	48 8b 0d 19 4e 00 00 	mov    0x4e19(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4207:	ba 1a 00 00 00       	mov    $0x1a,%edx
    420c:	be 01 00 00 00       	mov    $0x1,%esi
    4211:	48 8d 3d b8 1e 00 00 	lea    0x1eb8(%rip),%rdi        # 60d0 <_IO_stdin_used+0xd0>
    4218:	e8 83 e2 ff ff       	call   24a0 <fwrite@plt>
    421d:	eb bf                	jmp    41de <copy_file_contents+0x4e>
    421f:	48 8d 3d d9 1f 00 00 	lea    0x1fd9(%rip),%rdi        # 61ff <_IO_stdin_used+0x1ff>
    4226:	e8 55 f9 ff ff       	call   3b80 <fatal_error>
    422b:	48 8b 0d ee 4d 00 00 	mov    0x4dee(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4232:	ba 28 00 00 00       	mov    $0x28,%edx
    4237:	be 01 00 00 00       	mov    $0x1,%esi
    423c:	48 8d 3d dd 21 00 00 	lea    0x21dd(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    4243:	e8 58 e2 ff ff       	call   24a0 <fwrite@plt>
    4248:	bf 01 00 00 00       	mov    $0x1,%edi
    424d:	e8 2e e2 ff ff       	call   2480 <exit@plt>
    4252:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    425d:	0f 1f 00             	nopl   (%rax)

0000000000004260 <add_write_request>:
    4260:	f3 0f 1e fa          	endbr64
    4264:	8b 46 44             	mov    0x44(%rsi),%eax
    4267:	48 89 fa             	mov    %rdi,%rdx
    426a:	48 89 f7             	mov    %rsi,%rdi
    426d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    4273:	8d 70 01             	lea    0x1(%rax),%esi
    4276:	48 8b 07             	mov    (%rdi),%rax
    4279:	44 8b 00             	mov    (%rax),%r8d
    427c:	f6 c1 02             	test   $0x2,%cl
    427f:	74 00                	je     4281 <add_write_request+0x21>
    4281:	89 f0                	mov    %esi,%eax
    4283:	44 29 c0             	sub    %r8d,%eax
    4286:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4289:	0f 82 91 e2 ff ff    	jb     2520 <add_write_request.cold>
    428f:	c1 e9 0a             	shr    $0xa,%ecx
    4292:	48 83 ec 08          	sub    $0x8,%rsp
    4296:	8b 47 44             	mov    0x44(%rdi),%eax
    4299:	23 47 58             	and    0x58(%rdi),%eax
    429c:	83 e1 01             	and    $0x1,%ecx
    429f:	89 77 44             	mov    %esi,0x44(%rdi)
    42a2:	8b 72 08             	mov    0x8(%rdx),%esi
    42a5:	66 0f ef c0          	pxor   %xmm0,%xmm0
    42a9:	d3 e0                	shl    %cl,%eax
    42ab:	8b 4a 04             	mov    0x4(%rdx),%ecx
    42ae:	48 c1 e0 06          	shl    $0x6,%rax
    42b2:	48 03 47 38          	add    0x38(%rdi),%rax
    42b6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    42bc:	89 70 04             	mov    %esi,0x4(%rax)
    42bf:	48 8d 72 10          	lea    0x10(%rdx),%rsi
    42c3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    42c9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    42d1:	48 89 70 10          	mov    %rsi,0x10(%rax)
    42d5:	89 48 18             	mov    %ecx,0x18(%rax)
    42d8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    42df:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    42e7:	48 89 50 20          	mov    %rdx,0x20(%rax)
    42eb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    42ef:	e8 2c e0 ff ff       	call   2320 <io_uring_submit@plt>
    42f4:	31 c0                	xor    %eax,%eax
    42f6:	48 83 c4 08          	add    $0x8,%rsp
    42fa:	c3                   	ret
    42fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004300 <add_read_request>:
    4300:	f3 0f 1e fa          	endbr64
    4304:	41 55                	push   %r13
    4306:	41 89 fd             	mov    %edi,%r13d
    4309:	41 54                	push   %r12
    430b:	55                   	push   %rbp
    430c:	53                   	push   %rbx
    430d:	48 89 f3             	mov    %rsi,%rbx
    4310:	48 83 ec 08          	sub    $0x8,%rsp
    4314:	8b 46 44             	mov    0x44(%rsi),%eax
    4317:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
    431d:	48 8b 16             	mov    (%rsi),%rdx
    4320:	83 c0 01             	add    $0x1,%eax
    4323:	8b 32                	mov    (%rdx),%esi
    4325:	f6 c1 02             	test   $0x2,%cl
    4328:	74 00                	je     432a <add_read_request+0x2a>
    432a:	89 c2                	mov    %eax,%edx
    432c:	29 f2                	sub    %esi,%edx
    432e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4331:	0f 82 f9 e1 ff ff    	jb     2530 <add_read_request.cold>
    4337:	8b 6b 44             	mov    0x44(%rbx),%ebp
    433a:	c1 e9 0a             	shr    $0xa,%ecx
    433d:	89 43 44             	mov    %eax,0x44(%rbx)
    4340:	bf 20 00 00 00       	mov    $0x20,%edi
    4345:	83 e1 01             	and    $0x1,%ecx
    4348:	23 6b 58             	and    0x58(%rbx),%ebp
    434b:	d3 e5                	shl    %cl,%ebp
    434d:	48 c1 e5 06          	shl    $0x6,%rbp
    4351:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4355:	e8 96 e0 ff ff       	call   23f0 <malloc@plt>
    435a:	be 01 00 00 00       	mov    $0x1,%esi
    435f:	bf 00 20 00 00       	mov    $0x2000,%edi
    4364:	49 89 c4             	mov    %rax,%r12
    4367:	e8 14 e0 ff ff       	call   2380 <calloc@plt>
    436c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    4371:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4375:	48 89 df             	mov    %rbx,%rdi
    4378:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    437d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    4382:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    438b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    4393:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
    4397:	4c 89 65 20          	mov    %r12,0x20(%rbp)
    439b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
    43a2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    43aa:	48 89 45 10          	mov    %rax,0x10(%rbp)
    43ae:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
    43b6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    43be:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    43c2:	e8 59 df ff ff       	call   2320 <io_uring_submit@plt>
    43c7:	48 83 c4 08          	add    $0x8,%rsp
    43cb:	31 c0                	xor    %eax,%eax
    43cd:	5b                   	pop    %rbx
    43ce:	5d                   	pop    %rbp
    43cf:	41 5c                	pop    %r12
    43d1:	41 5d                	pop    %r13
    43d3:	c3                   	ret
    43d4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    43df:	90                   	nop

00000000000043e0 <_send_static_string_content>:
    43e0:	f3 0f 1e fa          	endbr64
    43e4:	41 56                	push   %r14
    43e6:	41 89 f6             	mov    %esi,%r14d
    43e9:	41 55                	push   %r13
    43eb:	49 89 fd             	mov    %rdi,%r13
    43ee:	bf 20 00 00 00       	mov    $0x20,%edi
    43f3:	41 54                	push   %r12
    43f5:	55                   	push   %rbp
    43f6:	48 89 d5             	mov    %rdx,%rbp
    43f9:	53                   	push   %rbx
    43fa:	e8 f1 df ff ff       	call   23f0 <malloc@plt>
    43ff:	48 85 c0             	test   %rax,%rax
    4402:	0f 84 dd 00 00 00    	je     44e5 <_send_static_string_content+0x105>
    4408:	48 89 c3             	mov    %rax,%rbx
    440b:	4c 89 ef             	mov    %r13,%rdi
    440e:	e8 ed de ff ff       	call   2300 <strlen@plt>
    4413:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    441a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    441e:	48 89 c7             	mov    %rax,%rdi
    4421:	49 89 c4             	mov    %rax,%r12
    4424:	e8 c7 df ff ff       	call   23f0 <malloc@plt>
    4429:	48 89 c7             	mov    %rax,%rdi
    442c:	48 85 c0             	test   %rax,%rax
    442f:	0f 84 b0 00 00 00    	je     44e5 <_send_static_string_content+0x105>
    4435:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4439:	4c 89 e2             	mov    %r12,%rdx
    443c:	4c 89 ee             	mov    %r13,%rsi
    443f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4443:	e8 78 df ff ff       	call   23c0 <memcpy@plt>
    4448:	8b 45 44             	mov    0x44(%rbp),%eax
    444b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
    4451:	8d 50 01             	lea    0x1(%rax),%edx
    4454:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4458:	8b 30                	mov    (%rax),%esi
    445a:	f6 c1 02             	test   $0x2,%cl
    445d:	0f 85 7d 00 00 00    	jne    44e0 <_send_static_string_content+0x100>
    4463:	89 d0                	mov    %edx,%eax
    4465:	29 f0                	sub    %esi,%eax
    4467:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    446a:	0f 82 ca e0 ff ff    	jb     253a <_send_static_string_content.cold>
    4470:	c1 e9 0a             	shr    $0xa,%ecx
    4473:	8b 45 44             	mov    0x44(%rbp),%eax
    4476:	23 45 58             	and    0x58(%rbp),%eax
    4479:	89 55 44             	mov    %edx,0x44(%rbp)
    447c:	83 e1 01             	and    $0x1,%ecx
    447f:	8b 53 04             	mov    0x4(%rbx),%edx
    4482:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    4488:	66 0f ef c0          	pxor   %xmm0,%xmm0
    448c:	d3 e0                	shl    %cl,%eax
    448e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    4491:	48 89 ef             	mov    %rbp,%rdi
    4494:	48 c1 e0 06          	shl    $0x6,%rax
    4498:	48 03 45 38          	add    0x38(%rbp),%rax
    449c:	89 48 04             	mov    %ecx,0x4(%rax)
    449f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
    44a3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    44a9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    44b1:	48 89 48 10          	mov    %rcx,0x10(%rax)
    44b5:	89 50 18             	mov    %edx,0x18(%rax)
    44b8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    44bf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    44c7:	48 89 58 20          	mov    %rbx,0x20(%rax)
    44cb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    44cf:	5b                   	pop    %rbx
    44d0:	5d                   	pop    %rbp
    44d1:	41 5c                	pop    %r12
    44d3:	41 5d                	pop    %r13
    44d5:	41 5e                	pop    %r14
    44d7:	e9 44 de ff ff       	jmp    2320 <io_uring_submit@plt>
    44dc:	0f 1f 40 00          	nopl   0x0(%rax)
    44e0:	e9 7e ff ff ff       	jmp    4463 <_send_static_string_content+0x83>
    44e5:	48 8b 0d 34 4b 00 00 	mov    0x4b34(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    44ec:	ba 28 00 00 00       	mov    $0x28,%edx
    44f1:	be 01 00 00 00       	mov    $0x1,%esi
    44f6:	48 8d 3d 23 1f 00 00 	lea    0x1f23(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    44fd:	e8 9e df ff ff       	call   24a0 <fwrite@plt>
    4502:	bf 01 00 00 00       	mov    $0x1,%edi
    4507:	e8 74 df ff ff       	call   2480 <exit@plt>
    450c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004510 <handle_unimplemented_method>:
    4510:	f3 0f 1e fa          	endbr64
    4514:	48 89 f2             	mov    %rsi,%rdx
    4517:	89 fe                	mov    %edi,%esi
    4519:	48 8b 3d f8 4a 00 00 	mov    0x4af8(%rip),%rdi        # 9018 <unimplemented_content>
    4520:	e9 bb fe ff ff       	jmp    43e0 <_send_static_string_content>
    4525:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004530 <handle_http_404>:
    4530:	f3 0f 1e fa          	endbr64
    4534:	48 89 f2             	mov    %rsi,%rdx
    4537:	89 fe                	mov    %edi,%esi
    4539:	48 8b 3d d0 4a 00 00 	mov    0x4ad0(%rip),%rdi        # 9010 <http_404_content>
    4540:	e9 9b fe ff ff       	jmp    43e0 <_send_static_string_content>
    4545:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004550 <handle_get_method>:
    4550:	f3 0f 1e fa          	endbr64
    4554:	41 56                	push   %r14
    4556:	41 55                	push   %r13
    4558:	49 89 d5             	mov    %rdx,%r13
    455b:	41 54                	push   %r12
    455d:	41 89 f4             	mov    %esi,%r12d
    4560:	55                   	push   %rbp
    4561:	48 89 fd             	mov    %rdi,%rbp
    4564:	53                   	push   %rbx
    4565:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    456c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4575:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    457d:	31 c0                	xor    %eax,%eax
    457f:	e8 7c dd ff ff       	call   2300 <strlen@plt>
    4584:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4589:	48 89 c3             	mov    %rax,%rbx
    458c:	0f 84 b6 00 00 00    	je     4648 <handle_get_method+0xf8>
    4592:	b8 69 63 00 00       	mov    $0x6369,%eax
    4597:	48 89 ee             	mov    %rbp,%rsi
    459a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    459e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    45a3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    45ab:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    45b3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    45be:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
    45c6:	e8 d5 dd ff ff       	call   23a0 <__memcpy_chk@plt>
    45cb:	48 89 e6             	mov    %rsp,%rsi
    45ce:	4c 89 f7             	mov    %r14,%rdi
    45d1:	e8 da dd ff ff       	call   23b0 <stat@plt>
    45d6:	83 f8 ff             	cmp    $0xffffffff,%eax
    45d9:	0f 84 d3 00 00 00    	je     46b2 <handle_get_method+0x162>
    45df:	8b 44 24 18          	mov    0x18(%rsp),%eax
    45e3:	25 00 f0 00 00       	and    $0xf000,%eax
    45e8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    45ed:	0f 84 f5 00 00 00    	je     46e8 <handle_get_method+0x198>
    45f3:	48 8b 3d 16 4a 00 00 	mov    0x4a16(%rip),%rdi        # 9010 <http_404_content>
    45fa:	4c 89 ea             	mov    %r13,%rdx
    45fd:	44 89 e6             	mov    %r12d,%esi
    4600:	e8 db fd ff ff       	call   43e0 <_send_static_string_content>
    4605:	4c 89 f2             	mov    %r14,%rdx
    4608:	bf 01 00 00 00       	mov    $0x1,%edi
    460d:	31 c0                	xor    %eax,%eax
    460f:	48 8d 35 0a 1b 00 00 	lea    0x1b0a(%rip),%rsi        # 6120 <_IO_stdin_used+0x120>
    4616:	e8 15 de ff ff       	call   2430 <__printf_chk@plt>
    461b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4623:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    462c:	0f 85 20 01 00 00    	jne    4752 <handle_get_method+0x202>
    4632:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    4639:	5b                   	pop    %rbx
    463a:	5d                   	pop    %rbp
    463b:	41 5c                	pop    %r12
    463d:	41 5d                	pop    %r13
    463f:	41 5e                	pop    %r14
    4641:	c3                   	ret
    4642:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4648:	ba 69 63 00 00       	mov    $0x6369,%edx
    464d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4655:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    465a:	48 89 ee             	mov    %rbp,%rsi
    465d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
    4665:	48 89 c2             	mov    %rax,%rdx
    4668:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4670:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    467b:	e8 20 dd ff ff       	call   23a0 <__memcpy_chk@plt>
    4680:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4685:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    468a:	48 8d 35 5a 1a 00 00 	lea    0x1a5a(%rip),%rsi        # 60eb <_IO_stdin_used+0xeb>
    4691:	48 29 d9             	sub    %rbx,%rcx
    4694:	ba 0b 00 00 00       	mov    $0xb,%edx
    4699:	e8 02 dd ff ff       	call   23a0 <__memcpy_chk@plt>
    469e:	48 89 e6             	mov    %rsp,%rsi
    46a1:	4c 89 f7             	mov    %r14,%rdi
    46a4:	e8 07 dd ff ff       	call   23b0 <stat@plt>
    46a9:	83 f8 ff             	cmp    $0xffffffff,%eax
    46ac:	0f 85 2d ff ff ff    	jne    45df <handle_get_method+0x8f>
    46b2:	4c 89 f2             	mov    %r14,%rdx
    46b5:	48 89 e9             	mov    %rbp,%rcx
    46b8:	48 8d 35 37 1a 00 00 	lea    0x1a37(%rip),%rsi        # 60f6 <_IO_stdin_used+0xf6>
    46bf:	31 c0                	xor    %eax,%eax
    46c1:	bf 01 00 00 00       	mov    $0x1,%edi
    46c6:	e8 65 dd ff ff       	call   2430 <__printf_chk@plt>
    46cb:	48 8b 3d 3e 49 00 00 	mov    0x493e(%rip),%rdi        # 9010 <http_404_content>
    46d2:	4c 89 ea             	mov    %r13,%rdx
    46d5:	44 89 e6             	mov    %r12d,%esi
    46d8:	e8 03 fd ff ff       	call   43e0 <_send_static_string_content>
    46dd:	e9 39 ff ff ff       	jmp    461b <handle_get_method+0xcb>
    46e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    46e8:	bf 70 00 00 00       	mov    $0x70,%edi
    46ed:	e8 fe dc ff ff       	call   23f0 <malloc@plt>
    46f2:	48 89 c3             	mov    %rax,%rbx
    46f5:	48 85 c0             	test   %rax,%rax
    46f8:	74 5d                	je     4757 <handle_get_method+0x207>
    46fa:	44 89 60 08          	mov    %r12d,0x8(%rax)
    46fe:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4703:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4707:	4c 89 f7             	mov    %r14,%rdi
    470a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
    4711:	e8 4a f5 ff ff       	call   3c60 <send_headers>
    4716:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    471b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    471f:	4c 89 f7             	mov    %r14,%rdi
    4722:	e8 69 fa ff ff       	call   4190 <copy_file_contents>
    4727:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    472c:	4c 89 f2             	mov    %r14,%rdx
    472f:	31 c0                	xor    %eax,%eax
    4731:	48 8d 35 d6 19 00 00 	lea    0x19d6(%rip),%rsi        # 610e <_IO_stdin_used+0x10e>
    4738:	bf 01 00 00 00       	mov    $0x1,%edi
    473d:	e8 ee dc ff ff       	call   2430 <__printf_chk@plt>
    4742:	4c 89 ee             	mov    %r13,%rsi
    4745:	48 89 df             	mov    %rbx,%rdi
    4748:	e8 13 fb ff ff       	call   4260 <add_write_request>
    474d:	e9 c9 fe ff ff       	jmp    461b <handle_get_method+0xcb>
    4752:	e8 b9 db ff ff       	call   2310 <__stack_chk_fail@plt>
    4757:	48 8b 0d c2 48 00 00 	mov    0x48c2(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    475e:	ba 28 00 00 00       	mov    $0x28,%edx
    4763:	be 01 00 00 00       	mov    $0x1,%esi
    4768:	48 8d 3d b1 1c 00 00 	lea    0x1cb1(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    476f:	e8 2c dd ff ff       	call   24a0 <fwrite@plt>
    4774:	bf 01 00 00 00       	mov    $0x1,%edi
    4779:	e8 02 dd ff ff       	call   2480 <exit@plt>
    477e:	66 90                	xchg   %ax,%ax

0000000000004780 <handle_http_method>:
    4780:	f3 0f 1e fa          	endbr64
    4784:	41 57                	push   %r15
    4786:	41 56                	push   %r14
    4788:	4c 8d 35 f6 18 00 00 	lea    0x18f6(%rip),%r14        # 6085 <_IO_stdin_used+0x85>
    478f:	41 55                	push   %r13
    4791:	49 89 d5             	mov    %rdx,%r13
    4794:	41 54                	push   %r12
    4796:	41 89 f4             	mov    %esi,%r12d
    4799:	4c 89 f6             	mov    %r14,%rsi
    479c:	55                   	push   %rbp
    479d:	53                   	push   %rbx
    479e:	48 83 ec 18          	sub    $0x18,%rsp
    47a2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    47ab:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    47b0:	31 c0                	xor    %eax,%eax
    47b2:	49 89 e7             	mov    %rsp,%r15
    47b5:	4c 89 fa             	mov    %r15,%rdx
    47b8:	e8 a3 db ff ff       	call   2360 <strtok_r@plt>
    47bd:	48 0f be 18          	movsbq (%rax),%rbx
    47c1:	48 89 c5             	mov    %rax,%rbp
    47c4:	84 db                	test   %bl,%bl
    47c6:	74 1d                	je     47e5 <handle_http_method+0x65>
    47c8:	e8 23 dd ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    47cd:	48 89 ea             	mov    %rbp,%rdx
    47d0:	48 8b 08             	mov    (%rax),%rcx
    47d3:	48 83 c2 01          	add    $0x1,%rdx
    47d7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    47da:	88 4a ff             	mov    %cl,-0x1(%rdx)
    47dd:	48 0f be 1a          	movsbq (%rdx),%rbx
    47e1:	84 db                	test   %bl,%bl
    47e3:	75 eb                	jne    47d0 <handle_http_method+0x50>
    47e5:	4c 89 fa             	mov    %r15,%rdx
    47e8:	4c 89 f6             	mov    %r14,%rsi
    47eb:	31 ff                	xor    %edi,%edi
    47ed:	e8 6e db ff ff       	call   2360 <strtok_r@plt>
    47f2:	48 8d 35 3a 19 00 00 	lea    0x193a(%rip),%rsi        # 6133 <_IO_stdin_used+0x133>
    47f9:	48 89 ef             	mov    %rbp,%rdi
    47fc:	48 89 c3             	mov    %rax,%rbx
    47ff:	e8 8c db ff ff       	call   2390 <strcmp@plt>
    4804:	4c 89 ea             	mov    %r13,%rdx
    4807:	44 89 e6             	mov    %r12d,%esi
    480a:	85 c0                	test   %eax,%eax
    480c:	75 2a                	jne    4838 <handle_http_method+0xb8>
    480e:	48 89 df             	mov    %rbx,%rdi
    4811:	e8 3a fd ff ff       	call   4550 <handle_get_method>
    4816:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    481b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4824:	75 20                	jne    4846 <handle_http_method+0xc6>
    4826:	48 83 c4 18          	add    $0x18,%rsp
    482a:	5b                   	pop    %rbx
    482b:	5d                   	pop    %rbp
    482c:	41 5c                	pop    %r12
    482e:	41 5d                	pop    %r13
    4830:	41 5e                	pop    %r14
    4832:	41 5f                	pop    %r15
    4834:	c3                   	ret
    4835:	0f 1f 00             	nopl   (%rax)
    4838:	48 8b 3d d9 47 00 00 	mov    0x47d9(%rip),%rdi        # 9018 <unimplemented_content>
    483f:	e8 9c fb ff ff       	call   43e0 <_send_static_string_content>
    4844:	eb d0                	jmp    4816 <handle_http_method+0x96>
    4846:	e8 c5 da ff ff       	call   2310 <__stack_chk_fail@plt>
    484b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004850 <get_line>:
    4850:	f3 0f 1e fa          	endbr64
    4854:	85 d2                	test   %edx,%edx
    4856:	7e 38                	jle    4890 <get_line+0x40>
    4858:	48 63 d2             	movslq %edx,%rdx
    485b:	48 83 c7 01          	add    $0x1,%rdi
    485f:	48 01 f2             	add    %rsi,%rdx
    4862:	eb 11                	jmp    4875 <get_line+0x25>
    4864:	0f 1f 40 00          	nopl   0x0(%rax)
    4868:	48 83 c6 01          	add    $0x1,%rsi
    486c:	48 83 c7 01          	add    $0x1,%rdi
    4870:	48 39 d6             	cmp    %rdx,%rsi
    4873:	74 1b                	je     4890 <get_line+0x40>
    4875:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4879:	88 06                	mov    %al,(%rsi)
    487b:	3c 0d                	cmp    $0xd,%al
    487d:	75 e9                	jne    4868 <get_line+0x18>
    487f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4882:	75 e4                	jne    4868 <get_line+0x18>
    4884:	c6 06 00             	movb   $0x0,(%rsi)
    4887:	31 c0                	xor    %eax,%eax
    4889:	c3                   	ret
    488a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4890:	b8 01 00 00 00       	mov    $0x1,%eax
    4895:	c3                   	ret
    4896:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000048a0 <handle_client_request>:
    48a0:	f3 0f 1e fa          	endbr64
    48a4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    48ab:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    48af:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    48b8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    48c0:	31 c0                	xor    %eax,%eax
    48c2:	49 89 e2             	mov    %rsp,%r10
    48c5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    48cd:	4c 89 d0             	mov    %r10,%rax
    48d0:	eb 13                	jmp    48e5 <handle_client_request+0x45>
    48d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    48d8:	48 83 c0 01          	add    $0x1,%rax
    48dc:	48 83 c1 01          	add    $0x1,%rcx
    48e0:	4c 39 c8             	cmp    %r9,%rax
    48e3:	74 4b                	je     4930 <handle_client_request+0x90>
    48e5:	44 0f b6 01          	movzbl (%rcx),%r8d
    48e9:	44 88 00             	mov    %r8b,(%rax)
    48ec:	41 80 f8 0d          	cmp    $0xd,%r8b
    48f0:	75 e6                	jne    48d8 <handle_client_request+0x38>
    48f2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    48f6:	75 e0                	jne    48d8 <handle_client_request+0x38>
    48f8:	c6 00 00             	movb   $0x0,(%rax)
    48fb:	8b 47 08             	mov    0x8(%rdi),%eax
    48fe:	48 89 f2             	mov    %rsi,%rdx
    4901:	4c 89 d7             	mov    %r10,%rdi
    4904:	89 c6                	mov    %eax,%esi
    4906:	e8 75 fe ff ff       	call   4780 <handle_http_method>
    490b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4913:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    491c:	75 39                	jne    4957 <handle_client_request+0xb7>
    491e:	31 c0                	xor    %eax,%eax
    4920:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4927:	c3                   	ret
    4928:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4930:	48 8b 0d e9 46 00 00 	mov    0x46e9(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4937:	ba 12 00 00 00       	mov    $0x12,%edx
    493c:	be 01 00 00 00       	mov    $0x1,%esi
    4941:	48 8d 3d ef 17 00 00 	lea    0x17ef(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    4948:	e8 53 db ff ff       	call   24a0 <fwrite@plt>
    494d:	bf 01 00 00 00       	mov    $0x1,%edi
    4952:	e8 29 db ff ff       	call   2480 <exit@plt>
    4957:	e8 b4 d9 ff ff       	call   2310 <__stack_chk_fail@plt>
    495c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004960 <add_accept_request>:
    4960:	f3 0f 1e fa          	endbr64
    4964:	55                   	push   %rbp
    4965:	53                   	push   %rbx
    4966:	48 89 cb             	mov    %rcx,%rbx
    4969:	48 83 ec 08          	sub    $0x8,%rsp
    496d:	8b 41 44             	mov    0x44(%rcx),%eax
    4970:	4c 8b 03             	mov    (%rbx),%r8
    4973:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
    4979:	83 c0 01             	add    $0x1,%eax
    497c:	45 8b 08             	mov    (%r8),%r9d
    497f:	f6 c1 02             	test   $0x2,%cl
    4982:	74 00                	je     4984 <add_accept_request+0x24>
    4984:	41 89 c0             	mov    %eax,%r8d
    4987:	45 29 c8             	sub    %r9d,%r8d
    498a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    498e:	0f 82 b6 db ff ff    	jb     254a <add_accept_request.cold>
    4994:	c1 e9 0a             	shr    $0xa,%ecx
    4997:	8b 6b 44             	mov    0x44(%rbx),%ebp
    499a:	23 6b 58             	and    0x58(%rbx),%ebp
    499d:	89 43 44             	mov    %eax,0x44(%rbx)
    49a0:	83 e1 01             	and    $0x1,%ecx
    49a3:	66 0f ef c0          	pxor   %xmm0,%xmm0
    49a7:	d3 e5                	shl    %cl,%ebp
    49a9:	48 c1 e5 06          	shl    $0x6,%rbp
    49ad:	48 03 6b 38          	add    0x38(%rbx),%rbp
    49b1:	89 7d 04             	mov    %edi,0x4(%rbp)
    49b4:	bf 10 00 00 00       	mov    $0x10,%edi
    49b9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
    49c0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    49c4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
    49c8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    49d0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
    49d8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    49dc:	e8 0f da ff ff       	call   23f0 <malloc@plt>
    49e1:	48 89 df             	mov    %rbx,%rdi
    49e4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    49ea:	48 89 45 20          	mov    %rax,0x20(%rbp)
    49ee:	48 83 c4 08          	add    $0x8,%rsp
    49f2:	5b                   	pop    %rbx
    49f3:	5d                   	pop    %rbp
    49f4:	e9 27 d9 ff ff       	jmp    2320 <io_uring_submit@plt>
    49f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004a00 <io_thread>:
    4a00:	f3 0f 1e fa          	endbr64
    4a04:	41 57                	push   %r15
    4a06:	31 d2                	xor    %edx,%edx
    4a08:	41 56                	push   %r14
    4a0a:	41 55                	push   %r13
    4a0c:	41 54                	push   %r12
    4a0e:	55                   	push   %rbp
    4a0f:	48 89 fd             	mov    %rdi,%rbp
    4a12:	53                   	push   %rbx
    4a13:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    4a1a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4a23:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4a2b:	48 8b 47 40          	mov    0x40(%rdi),%rax
    4a2f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4a34:	bf 00 01 00 00       	mov    $0x100,%edi
    4a39:	48 89 de             	mov    %rbx,%rsi
    4a3c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4a40:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4a45:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4a4a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4a4f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4a54:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4a5c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4a61:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4a69:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4a6e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4a76:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4a7b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4a83:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4a88:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4a90:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4a95:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4a9d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4aa5:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4aad:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4ab5:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4abd:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4ac5:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4acd:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4ad5:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4add:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4ae5:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4aed:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4af4:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
    4afc:	e8 cf d8 ff ff       	call   23d0 <io_uring_queue_init@plt>
    4b01:	48 8b 7d 40          	mov    0x40(%rbp),%rdi
    4b05:	31 f6                	xor    %esi,%esi
    4b07:	e8 b4 d9 ff ff       	call   24c0 <io_uring_register_eventfd@plt>
    4b0c:	31 d2                	xor    %edx,%edx
    4b0e:	be 01 00 00 00       	mov    $0x1,%esi
    4b13:	bf 02 00 00 00       	mov    $0x2,%edi
    4b18:	e8 f3 d9 ff ff       	call   2510 <socket@plt>
    4b1d:	83 f8 ff             	cmp    $0xffffffff,%eax
    4b20:	0f 84 08 06 00 00    	je     512e <io_thread+0x72e>
    4b26:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4b2b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4b31:	89 c7                	mov    %eax,%edi
    4b33:	41 89 c4             	mov    %eax,%r12d
    4b36:	ba 02 00 00 00       	mov    $0x2,%edx
    4b3b:	be 01 00 00 00       	mov    $0x1,%esi
    4b40:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    4b48:	e8 93 d7 ff ff       	call   22e0 <setsockopt@plt>
    4b4d:	85 c0                	test   %eax,%eax
    4b4f:	0f 88 cd 05 00 00    	js     5122 <io_thread+0x722>
    4b55:	8b 05 95 1e 00 00    	mov    0x1e95(%rip),%eax        # 69f0 <_IO_stdin_used+0x9f0>
    4b5b:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    4b60:	ba 10 00 00 00       	mov    $0x10,%edx
    4b65:	44 89 e7             	mov    %r12d,%edi
    4b68:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4b71:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    4b79:	89 44 24 40          	mov    %eax,0x40(%rsp)
    4b7d:	e8 be d8 ff ff       	call   2440 <bind@plt>
    4b82:	85 c0                	test   %eax,%eax
    4b84:	0f 88 8c 05 00 00    	js     5116 <io_thread+0x716>
    4b8a:	be 0a 00 00 00       	mov    $0xa,%esi
    4b8f:	44 89 e7             	mov    %r12d,%edi
    4b92:	e8 69 d8 ff ff       	call   2400 <listen@plt>
    4b97:	85 c0                	test   %eax,%eax
    4b99:	0f 88 6b 05 00 00    	js     510a <io_thread+0x70a>
    4b9f:	ba db 18 00 00       	mov    $0x18db,%edx
    4ba4:	48 8d 35 d1 15 00 00 	lea    0x15d1(%rip),%rsi        # 617c <_IO_stdin_used+0x17c>
    4bab:	bf 01 00 00 00       	mov    $0x1,%edi
    4bb0:	31 c0                	xor    %eax,%eax
    4bb2:	e8 79 d8 ff ff       	call   2430 <__printf_chk@plt>
    4bb7:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4bbc:	48 89 d9             	mov    %rbx,%rcx
    4bbf:	44 89 e7             	mov    %r12d,%edi
    4bc2:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4bc7:	48 89 c6             	mov    %rax,%rsi
    4bca:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    4bcf:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    4bd4:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
    4bdc:	e8 7f fd ff ff       	call   4960 <add_accept_request>
    4be1:	bf 01 00 00 00       	mov    $0x1,%edi
    4be6:	be 10 00 00 00       	mov    $0x10,%esi
    4beb:	e8 90 d7 ff ff       	call   2380 <calloc@plt>
    4bf0:	bf 0a 00 00 00       	mov    $0xa,%edi
    4bf5:	49 89 c5             	mov    %rax,%r13
    4bf8:	e8 f3 d7 ff ff       	call   23f0 <malloc@plt>
    4bfd:	48 85 c0             	test   %rax,%rax
    4c00:	0f 84 dd 04 00 00    	je     50e3 <io_thread+0x6e3>
    4c06:	49 89 45 00          	mov    %rax,0x0(%r13)
    4c0a:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4c11:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4c18:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
    4c20:	8d 50 01             	lea    0x1(%rax),%edx
    4c23:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4c28:	8b 30                	mov    (%rax),%esi
    4c2a:	f6 c1 02             	test   $0x2,%cl
    4c2d:	0f 85 2d 04 00 00    	jne    5060 <io_thread+0x660>
    4c33:	89 d0                	mov    %edx,%eax
    4c35:	29 f0                	sub    %esi,%eax
    4c37:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4c3e:	0f 82 10 d9 ff ff    	jb     2554 <io_thread.cold>
    4c44:	c1 e9 0a             	shr    $0xa,%ecx
    4c47:	48 8d 75 48          	lea    0x48(%rbp),%rsi
    4c4b:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4c4f:	48 89 df             	mov    %rbx,%rdi
    4c52:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4c59:	83 e1 01             	and    $0x1,%ecx
    4c5c:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    4c63:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    4c6a:	d3 e0                	shl    %cl,%eax
    4c6c:	8b 55 48             	mov    0x48(%rbp),%edx
    4c6f:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4c74:	48 c1 e0 06          	shl    $0x6,%rax
    4c78:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    4c80:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    4c86:	89 50 04             	mov    %edx,0x4(%rax)
    4c89:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4c91:	4c 89 68 10          	mov    %r13,0x10(%rax)
    4c95:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    4c9d:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4ca5:	48 89 70 20          	mov    %rsi,0x20(%rax)
    4ca9:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    4cad:	e8 6e d6 ff ff       	call   2320 <io_uring_submit@plt>
    4cb2:	83 7d 2c 01          	cmpl   $0x1,0x2c(%rbp)
    4cb6:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4cbb:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4cc3:	0f 85 b8 01 00 00    	jne    4e81 <io_thread+0x481>
    4cc9:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4cce:	4d 89 ce             	mov    %r9,%r14
    4cd1:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4cd6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4ce0:	48 8d 3d ab 14 00 00 	lea    0x14ab(%rip),%rdi        # 6192 <_IO_stdin_used+0x192>
    4ce7:	e8 e4 d5 ff ff       	call   22d0 <puts@plt>
    4cec:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4cf3:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
    4cfa:	c1 e9 0b             	shr    $0xb,%ecx
    4cfd:	83 e1 01             	and    $0x1,%ecx
    4d00:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4d08:	8b 00                	mov    (%rax),%eax
    4d0a:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    4d12:	8b 16                	mov    (%rsi),%edx
    4d14:	39 d0                	cmp    %edx,%eax
    4d16:	74 36                	je     4d4e <io_thread+0x34e>
    4d18:	89 f8                	mov    %edi,%eax
    4d1a:	21 d0                	and    %edx,%eax
    4d1c:	d3 e0                	shl    %cl,%eax
    4d1e:	48 c1 e0 04          	shl    $0x4,%rax
    4d22:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
    4d2a:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    4d32:	0f 85 88 01 00 00    	jne    4ec0 <io_thread+0x4c0>
    4d38:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4d3c:	0f 85 26 03 00 00    	jne    5068 <io_thread+0x668>
    4d42:	8b 40 08             	mov    0x8(%rax),%eax
    4d45:	83 c2 01             	add    $0x1,%edx
    4d48:	89 16                	mov    %edx,(%rsi)
    4d4a:	85 c0                	test   %eax,%eax
    4d4c:	79 b2                	jns    4d00 <io_thread+0x300>
    4d4e:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    4d57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4d60:	45 31 c0             	xor    %r8d,%r8d
    4d63:	31 d2                	xor    %edx,%edx
    4d65:	b9 01 00 00 00       	mov    $0x1,%ecx
    4d6a:	4c 89 f6             	mov    %r14,%rsi
    4d6d:	48 89 df             	mov    %rbx,%rdi
    4d70:	e8 ab d6 ff ff       	call   2420 <__io_uring_get_cqe@plt>
    4d75:	41 89 c7             	mov    %eax,%r15d
    4d78:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4d7d:	48 83 38 01          	cmpq   $0x1,(%rax)
    4d81:	0f 84 f1 02 00 00    	je     5078 <io_thread+0x678>
    4d87:	48 8d 3d 2a 14 00 00 	lea    0x142a(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4d8e:	e8 3d d5 ff ff       	call   22d0 <puts@plt>
    4d93:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4d98:	4c 8b 22             	mov    (%rdx),%r12
    4d9b:	45 85 ff             	test   %r15d,%r15d
    4d9e:	0f 88 2e 03 00 00    	js     50d2 <io_thread+0x6d2>
    4da4:	8b 42 08             	mov    0x8(%rdx),%eax
    4da7:	45 8b 04 24          	mov    (%r12),%r8d
    4dab:	85 c0                	test   %eax,%eax
    4dad:	0f 88 e5 02 00 00    	js     5098 <io_thread+0x698>
    4db3:	41 83 f8 01          	cmp    $0x1,%r8d
    4db7:	0f 84 3b 01 00 00    	je     4ef8 <io_thread+0x4f8>
    4dbd:	41 83 f8 02          	cmp    $0x2,%r8d
    4dc1:	0f 84 b1 01 00 00    	je     4f78 <io_thread+0x578>
    4dc7:	45 85 c0             	test   %r8d,%r8d
    4dca:	0f 84 70 01 00 00    	je     4f40 <io_thread+0x540>
    4dd0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    4dd8:	8b 02                	mov    (%rdx),%eax
    4dda:	83 c0 01             	add    $0x1,%eax
    4ddd:	89 02                	mov    %eax,(%rdx)
    4ddf:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4de6:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4ded:	8d 50 01             	lea    0x1(%rax),%edx
    4df0:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4df5:	8b 30                	mov    (%rax),%esi
    4df7:	f6 c1 02             	test   $0x2,%cl
    4dfa:	74 00                	je     4dfc <io_thread+0x3fc>
    4dfc:	89 d0                	mov    %edx,%eax
    4dfe:	29 f0                	sub    %esi,%eax
    4e00:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4e07:	0f 82 47 d7 ff ff    	jb     2554 <io_thread.cold>
    4e0d:	c1 e9 0a             	shr    $0xa,%ecx
    4e10:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    4e15:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4e19:	48 89 df             	mov    %rbx,%rdi
    4e1c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4e23:	83 e1 01             	and    $0x1,%ecx
    4e26:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    4e2d:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    4e34:	d3 e0                	shl    %cl,%eax
    4e36:	8b 55 48             	mov    0x48(%rbp),%edx
    4e39:	48 c1 e0 06          	shl    $0x6,%rax
    4e3d:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    4e45:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    4e4b:	89 50 04             	mov    %edx,0x4(%rax)
    4e4e:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4e56:	4c 89 68 10          	mov    %r13,0x10(%rax)
    4e5a:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    4e62:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4e6a:	48 89 70 20          	mov    %rsi,0x20(%rax)
    4e6e:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    4e72:	e8 a9 d4 ff ff       	call   2320 <io_uring_submit@plt>
    4e77:	83 7d 2c 01          	cmpl   $0x1,0x2c(%rbp)
    4e7b:	0f 84 5f fe ff ff    	je     4ce0 <io_thread+0x2e0>
    4e81:	48 8d 3d 69 13 00 00 	lea    0x1369(%rip),%rdi        # 61f1 <_IO_stdin_used+0x1f1>
    4e88:	e8 43 d4 ff ff       	call   22d0 <puts@plt>
    4e8d:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    4e95:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4e9e:	0f 85 3a 02 00 00    	jne    50de <io_thread+0x6de>
    4ea4:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    4eab:	31 c0                	xor    %eax,%eax
    4ead:	5b                   	pop    %rbx
    4eae:	5d                   	pop    %rbp
    4eaf:	41 5c                	pop    %r12
    4eb1:	41 5d                	pop    %r13
    4eb3:	41 5e                	pop    %r14
    4eb5:	41 5f                	pop    %r15
    4eb7:	c3                   	ret
    4eb8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4ec0:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    4ec5:	48 85 c0             	test   %rax,%rax
    4ec8:	0f 84 92 fe ff ff    	je     4d60 <io_thread+0x360>
    4ece:	48 83 38 01          	cmpq   $0x1,(%rax)
    4ed2:	0f 84 a0 01 00 00    	je     5078 <io_thread+0x678>
    4ed8:	48 8d 3d d9 12 00 00 	lea    0x12d9(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4edf:	e8 ec d3 ff ff       	call   22d0 <puts@plt>
    4ee4:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4ee9:	4c 8b 22             	mov    (%rdx),%r12
    4eec:	e9 b3 fe ff ff       	jmp    4da4 <io_thread+0x3a4>
    4ef1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4ef8:	85 c0                	test   %eax,%eax
    4efa:	0f 85 c0 00 00 00    	jne    4fc0 <io_thread+0x5c0>
    4f00:	48 8b 0d 19 41 00 00 	mov    0x4119(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4f07:	ba 0f 00 00 00       	mov    $0xf,%edx
    4f0c:	be 01 00 00 00       	mov    $0x1,%esi
    4f11:	48 8d 3d c9 12 00 00 	lea    0x12c9(%rip),%rdi        # 61e1 <_IO_stdin_used+0x1e1>
    4f18:	e8 83 d5 ff ff       	call   24a0 <fwrite@plt>
    4f1d:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4f22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4f28:	48 85 c0             	test   %rax,%rax
    4f2b:	0f 84 ae fe ff ff    	je     4ddf <io_thread+0x3df>
    4f31:	e9 9a fe ff ff       	jmp    4dd0 <io_thread+0x3d0>
    4f36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4f40:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    4f45:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    4f4a:	48 89 d9             	mov    %rbx,%rcx
    4f4d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    4f51:	e8 0a fa ff ff       	call   4960 <add_accept_request>
    4f56:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4f5b:	48 89 de             	mov    %rbx,%rsi
    4f5e:	8b 78 08             	mov    0x8(%rax),%edi
    4f61:	e8 9a f3 ff ff       	call   4300 <add_read_request>
    4f66:	4c 89 e7             	mov    %r12,%rdi
    4f69:	e8 42 d3 ff ff       	call   22b0 <free@plt>
    4f6e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4f73:	eb b3                	jmp    4f28 <io_thread+0x528>
    4f75:	0f 1f 00             	nopl   (%rax)
    4f78:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    4f7d:	45 31 ff             	xor    %r15d,%r15d
    4f80:	85 c0                	test   %eax,%eax
    4f82:	7e 20                	jle    4fa4 <io_thread+0x5a4>
    4f84:	0f 1f 40 00          	nopl   0x0(%rax)
    4f88:	4c 89 f8             	mov    %r15,%rax
    4f8b:	49 83 c7 01          	add    $0x1,%r15
    4f8f:	48 c1 e0 04          	shl    $0x4,%rax
    4f93:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    4f98:	e8 13 d3 ff ff       	call   22b0 <free@plt>
    4f9d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    4fa2:	7f e4                	jg     4f88 <io_thread+0x588>
    4fa4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    4fa9:	e8 a2 d3 ff ff       	call   2350 <close@plt>
    4fae:	4c 89 e7             	mov    %r12,%rdi
    4fb1:	e8 fa d2 ff ff       	call   22b0 <free@plt>
    4fb6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4fbb:	e9 68 ff ff ff       	jmp    4f28 <io_thread+0x528>
    4fc0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    4fc5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4fca:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    4fd2:	eb 11                	jmp    4fe5 <io_thread+0x5e5>
    4fd4:	0f 1f 40 00          	nopl   0x0(%rax)
    4fd8:	48 83 c0 01          	add    $0x1,%rax
    4fdc:	48 83 c2 01          	add    $0x1,%rdx
    4fe0:	48 39 c6             	cmp    %rax,%rsi
    4fe3:	74 4b                	je     5030 <io_thread+0x630>
    4fe5:	0f b6 0a             	movzbl (%rdx),%ecx
    4fe8:	88 08                	mov    %cl,(%rax)
    4fea:	80 f9 0d             	cmp    $0xd,%cl
    4fed:	75 e9                	jne    4fd8 <io_thread+0x5d8>
    4fef:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    4ff3:	75 e3                	jne    4fd8 <io_thread+0x5d8>
    4ff5:	c6 00 00             	movb   $0x0,(%rax)
    4ff8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    4ffd:	48 89 da             	mov    %rbx,%rdx
    5000:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5005:	e8 76 f7 ff ff       	call   4780 <handle_http_method>
    500a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    500f:	e8 9c d2 ff ff       	call   22b0 <free@plt>
    5014:	4c 89 e7             	mov    %r12,%rdi
    5017:	e8 94 d2 ff ff       	call   22b0 <free@plt>
    501c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5021:	e9 02 ff ff ff       	jmp    4f28 <io_thread+0x528>
    5026:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5030:	48 8b 0d e9 3f 00 00 	mov    0x3fe9(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    5037:	ba 12 00 00 00       	mov    $0x12,%edx
    503c:	be 01 00 00 00       	mov    $0x1,%esi
    5041:	48 8d 3d ef 10 00 00 	lea    0x10ef(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    5048:	e8 53 d4 ff ff       	call   24a0 <fwrite@plt>
    504d:	bf 01 00 00 00       	mov    $0x1,%edi
    5052:	e8 29 d4 ff ff       	call   2480 <exit@plt>
    5057:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    5060:	e9 ce fb ff ff       	jmp    4c33 <io_thread+0x233>
    5065:	0f 1f 00             	nopl   (%rax)
    5068:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    506d:	e9 5c fe ff ff       	jmp    4ece <io_thread+0x4ce>
    5072:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5078:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5080:	48 8d 3d 1d 11 00 00 	lea    0x111d(%rip),%rdi        # 61a4 <_IO_stdin_used+0x1a4>
    5087:	8b 02                	mov    (%rdx),%eax
    5089:	83 c0 01             	add    $0x1,%eax
    508c:	89 02                	mov    %eax,(%rdx)
    508e:	e8 3d d2 ff ff       	call   22d0 <puts@plt>
    5093:	e9 e9 fd ff ff       	jmp    4e81 <io_thread+0x481>
    5098:	f7 d8                	neg    %eax
    509a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    509f:	89 c7                	mov    %eax,%edi
    50a1:	e8 3a d4 ff ff       	call   24e0 <strerror@plt>
    50a6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    50ab:	be 01 00 00 00       	mov    $0x1,%esi
    50b0:	48 8b 3d 69 3f 00 00 	mov    0x3f69(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    50b7:	48 89 c1             	mov    %rax,%rcx
    50ba:	48 8d 15 8f 13 00 00 	lea    0x138f(%rip),%rdx        # 6450 <_IO_stdin_used+0x450>
    50c1:	31 c0                	xor    %eax,%eax
    50c3:	e8 e8 d3 ff ff       	call   24b0 <__fprintf_chk@plt>
    50c8:	bf 01 00 00 00       	mov    $0x1,%edi
    50cd:	e8 ae d3 ff ff       	call   2480 <exit@plt>
    50d2:	48 8d 3d f6 10 00 00 	lea    0x10f6(%rip),%rdi        # 61cf <_IO_stdin_used+0x1cf>
    50d9:	e8 a2 ea ff ff       	call   3b80 <fatal_error>
    50de:	e8 2d d2 ff ff       	call   2310 <__stack_chk_fail@plt>
    50e3:	48 8b 0d 36 3f 00 00 	mov    0x3f36(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    50ea:	ba 28 00 00 00       	mov    $0x28,%edx
    50ef:	be 01 00 00 00       	mov    $0x1,%esi
    50f4:	48 8d 3d 25 13 00 00 	lea    0x1325(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    50fb:	e8 a0 d3 ff ff       	call   24a0 <fwrite@plt>
    5100:	bf 01 00 00 00       	mov    $0x1,%edi
    5105:	e8 76 d3 ff ff       	call   2480 <exit@plt>
    510a:	48 8d 3d 62 10 00 00 	lea    0x1062(%rip),%rdi        # 6173 <_IO_stdin_used+0x173>
    5111:	e8 6a ea ff ff       	call   3b80 <fatal_error>
    5116:	48 8d 3d 4f 10 00 00 	lea    0x104f(%rip),%rdi        # 616c <_IO_stdin_used+0x16c>
    511d:	e8 5e ea ff ff       	call   3b80 <fatal_error>
    5122:	48 8d 3d 2a 10 00 00 	lea    0x102a(%rip),%rdi        # 6153 <_IO_stdin_used+0x153>
    5129:	e8 52 ea ff ff       	call   3b80 <fatal_error>
    512e:	48 8d 3d 15 10 00 00 	lea    0x1015(%rip),%rdi        # 614a <_IO_stdin_used+0x14a>
    5135:	e8 46 ea ff ff       	call   3b80 <fatal_error>
    513a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005140 <receive>:
    5140:	f3 0f 1e fa          	endbr64
    5144:	8b 87 34 01 00 00    	mov    0x134(%rdi),%eax
    514a:	85 c0                	test   %eax,%eax
    514c:	0f 8e ed 00 00 00    	jle    523f <receive+0xff>
    5152:	41 54                	push   %r12
    5154:	4c 63 e0             	movslq %eax,%r12
    5157:	48 89 fa             	mov    %rdi,%rdx
    515a:	55                   	push   %rbp
    515b:	49 c1 e4 05          	shl    $0x5,%r12
    515f:	53                   	push   %rbx
    5160:	48 8b b7 28 02 00 00 	mov    0x228(%rdi),%rsi
    5167:	49 01 f4             	add    %rsi,%r12
    516a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5170:	48 8b 2e             	mov    (%rsi),%rbp
    5173:	48 8b bd 80 00 00 00 	mov    0x80(%rbp),%rdi
    517a:	48 85 ff             	test   %rdi,%rdi
    517d:	0f 8e 9d 00 00 00    	jle    5220 <receive+0xe0>
    5183:	48 8b 8a 30 02 00 00 	mov    0x230(%rdx),%rcx
    518a:	4c 8b 45 00          	mov    0x0(%rbp),%r8
    518e:	4c 63 1a             	movslq (%rdx),%r11
    5191:	49 89 c9             	mov    %rcx,%r9
    5194:	48 8d 41 01          	lea    0x1(%rcx),%rax
    5198:	49 f7 d9             	neg    %r9
    519b:	48 01 c7             	add    %rax,%rdi
    519e:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
    51a2:	4c 8b 8a 08 01 00 00 	mov    0x108(%rdx),%r9
    51a9:	4c 8b 46 18          	mov    0x18(%rsi),%r8
    51ad:	49 29 c9             	sub    %rcx,%r9
    51b0:	49 29 c8             	sub    %rcx,%r8
    51b3:	eb 0c                	jmp    51c1 <receive+0x81>
    51b5:	0f 1f 00             	nopl   (%rax)
    51b8:	48 83 c0 01          	add    $0x1,%rax
    51bc:	48 39 f8             	cmp    %rdi,%rax
    51bf:	74 5f                	je     5220 <receive+0xe0>
    51c1:	49 8d 0c 01          	lea    (%r9,%rax,1),%rcx
    51c5:	48 89 82 30 02 00 00 	mov    %rax,0x230(%rdx)
    51cc:	48 89 8a 08 01 00 00 	mov    %rcx,0x108(%rdx)
    51d3:	49 8d 0c 00          	lea    (%r8,%rax,1),%rcx
    51d7:	48 89 4e 18          	mov    %rcx,0x18(%rsi)
    51db:	49 8b 4c c2 f8       	mov    -0x8(%r10,%rax,8),%rcx
    51e0:	4c 39 59 10          	cmp    %r11,0x10(%rcx)
    51e4:	75 d2                	jne    51b8 <receive+0x78>
    51e6:	48 63 9a 30 01 00 00 	movslq 0x130(%rdx),%rbx
    51ed:	48 39 59 08          	cmp    %rbx,0x8(%rcx)
    51f1:	75 c5                	jne    51b8 <receive+0x78>
    51f3:	bf 01 00 00 00       	mov    $0x1,%edi
    51f8:	b9 01 00 00 00       	mov    $0x1,%ecx
    51fd:	ba 01 00 00 00       	mov    $0x1,%edx
    5202:	31 c0                	xor    %eax,%eax
    5204:	48 8d 35 6d 12 00 00 	lea    0x126d(%rip),%rsi        # 6478 <_IO_stdin_used+0x478>
    520b:	e8 20 d2 ff ff       	call   2430 <__printf_chk@plt>
    5210:	bf 01 00 00 00       	mov    $0x1,%edi
    5215:	e8 66 d2 ff ff       	call   2480 <exit@plt>
    521a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5220:	48 c7 85 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rbp)
    522b:	48 83 c6 20          	add    $0x20,%rsi
    522f:	49 39 f4             	cmp    %rsi,%r12
    5232:	0f 85 38 ff ff ff    	jne    5170 <receive+0x30>
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
    5250:	f3 0f 1e fa          	endbr64
    5254:	41 57                	push   %r15
    5256:	41 56                	push   %r14
    5258:	41 55                	push   %r13
    525a:	41 54                	push   %r12
    525c:	55                   	push   %rbp
    525d:	53                   	push   %rbx
    525e:	48 89 fb             	mov    %rdi,%rbx
    5261:	48 83 ec 28          	sub    $0x28,%rsp
    5265:	8b 07                	mov    (%rdi),%eax
    5267:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    526d:	0f 84 5d 01 00 00    	je     53d0 <barriered_work+0x180>
    5273:	e8 c8 fe ff ff       	call   5140 <receive>
    5278:	83 bb 00 02 00 00 01 	cmpl   $0x1,0x200(%rbx)
    527f:	75 1b                	jne    529c <barriered_work+0x4c>
    5281:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5288:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    5290:	0f ae f8             	sfence
    5293:	83 bb 00 02 00 00 01 	cmpl   $0x1,0x200(%rbx)
    529a:	74 ec                	je     5288 <barriered_work+0x38>
    529c:	83 bb 38 02 00 00 01 	cmpl   $0x1,0x238(%rbx)
    52a3:	74 14                	je     52b9 <barriered_work+0x69>
    52a5:	0f ae f0             	mfence
    52a8:	48 83 c4 28          	add    $0x28,%rsp
    52ac:	31 c0                	xor    %eax,%eax
    52ae:	5b                   	pop    %rbx
    52af:	5d                   	pop    %rbp
    52b0:	41 5c                	pop    %r12
    52b2:	41 5d                	pop    %r13
    52b4:	41 5e                	pop    %r14
    52b6:	41 5f                	pop    %r15
    52b8:	c3                   	ret
    52b9:	48 63 83 34 01 00 00 	movslq 0x134(%rbx),%rax
    52c0:	85 c0                	test   %eax,%eax
    52c2:	7e e1                	jle    52a5 <barriered_work+0x55>
    52c4:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    52c9:	48 8d 83 40 02 00 00 	lea    0x240(%rbx),%rax
    52d0:	44 8b b3 30 01 00 00 	mov    0x130(%rbx),%r14d
    52d7:	31 c9                	xor    %ecx,%ecx
    52d9:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    52de:	48 8d 83 48 02 00 00 	lea    0x248(%rbx),%rax
    52e5:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    52ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    52f0:	41 39 ce             	cmp    %ecx,%r14d
    52f3:	0f 84 bc 00 00 00    	je     53b5 <barriered_work+0x165>
    52f9:	49 89 c9             	mov    %rcx,%r9
    52fc:	49 c1 e1 05          	shl    $0x5,%r9
    5300:	4c 03 8b 28 02 00 00 	add    0x228(%rbx),%r9
    5307:	4d 8b 51 08          	mov    0x8(%r9),%r10
    530b:	49 8b aa 80 00 00 00 	mov    0x80(%r10),%rbp
    5312:	4d 63 82 88 00 00 00 	movslq 0x88(%r10),%r8
    5319:	4c 39 c5             	cmp    %r8,%rbp
    531c:	0f 8d 93 00 00 00    	jge    53b5 <barriered_work+0x165>
    5322:	4d 89 c3             	mov    %r8,%r11
    5325:	4c 8b ab 08 01 00 00 	mov    0x108(%rbx),%r13
    532c:	4d 8b 61 10          	mov    0x10(%r9),%r12
    5330:	49 29 eb             	sub    %rbp,%r11
    5333:	49 8b 3a             	mov    (%r10),%rdi
    5336:	49 8d 43 ff          	lea    -0x1(%r11),%rax
    533a:	48 83 f8 02          	cmp    $0x2,%rax
    533e:	0f 86 5c 02 00 00    	jbe    55a0 <barriered_work+0x350>
    5344:	48 8d 04 ed 00 00 00 00 	lea    0x0(,%rbp,8),%rax
    534c:	4a 8d 34 c5 00 00 00 00 	lea    0x0(,%r8,8),%rsi
    5354:	48 8d 14 07          	lea    (%rdi,%rax,1),%rdx
    5358:	4c 8d 3c 37          	lea    (%rdi,%rsi,1),%r15
    535c:	4c 39 7c 24 10       	cmp    %r15,0x10(%rsp)
    5361:	0f 83 e9 01 00 00    	jae    5550 <barriered_work+0x300>
    5367:	4c 8b 7c 24 18       	mov    0x18(%rsp),%r15
    536c:	4c 39 fa             	cmp    %r15,%rdx
    536f:	0f 83 db 01 00 00    	jae    5550 <barriered_work+0x300>
    5375:	48 01 f8             	add    %rdi,%rax
    5378:	48 01 fe             	add    %rdi,%rsi
    537b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5380:	4c 8b bb 40 02 00 00 	mov    0x240(%rbx),%r15
    5387:	48 83 c0 08          	add    $0x8,%rax
    538b:	4c 89 78 f8          	mov    %r15,-0x8(%rax)
    538f:	48 39 f0             	cmp    %rsi,%rax
    5392:	75 ec                	jne    5380 <barriered_work+0x130>
    5394:	0f 1f 40 00          	nopl   0x0(%rax)
    5398:	4d 01 dd             	add    %r11,%r13
    539b:	4d 01 dc             	add    %r11,%r12
    539e:	4c 89 ab 08 01 00 00 	mov    %r13,0x108(%rbx)
    53a5:	4d 89 61 10          	mov    %r12,0x10(%r9)
    53a9:	4d 89 82 80 00 00 00 	mov    %r8,0x80(%r10)
    53b0:	4e 89 7c c7 f8       	mov    %r15,-0x8(%rdi,%r8,8)
    53b5:	48 83 c1 01          	add    $0x1,%rcx
    53b9:	48 39 4c 24 08       	cmp    %rcx,0x8(%rsp)
    53be:	0f 85 2c ff ff ff    	jne    52f0 <barriered_work+0xa0>
    53c4:	e9 dc fe ff ff       	jmp    52a5 <barriered_work+0x55>
    53c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    53d0:	e8 6b fd ff ff       	call   5140 <receive>
    53d5:	8b 8b 34 01 00 00    	mov    0x134(%rbx),%ecx
    53db:	8b 03                	mov    (%rbx),%eax
    53dd:	85 c9                	test   %ecx,%ecx
    53df:	0f 8e 8e 00 00 00    	jle    5473 <barriered_work+0x223>
    53e5:	48 63 d0             	movslq %eax,%rdx
    53e8:	83 c0 01             	add    $0x1,%eax
    53eb:	4c 63 d1             	movslq %ecx,%r10
    53ee:	4c 8d 1c 92          	lea    (%rdx,%rdx,4),%r11
    53f2:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    53f9:	49 c1 e2 05          	shl    $0x5,%r10
    53fd:	49 c1 e3 07          	shl    $0x7,%r11
    5401:	48 8b 6a 10          	mov    0x10(%rdx),%rbp
    5405:	99                   	cltd
    5406:	f7 f9                	idiv   %ecx
    5408:	4c 8d 6d 20          	lea    0x20(%rbp),%r13
    540c:	89 d0                	mov    %edx,%eax
    540e:	f7 d8                	neg    %eax
    5410:	0f 48 c2             	cmovs  %edx,%eax
    5413:	31 ff                	xor    %edi,%edi
    5415:	45 31 e4             	xor    %r12d,%r12d
    5418:	48 98                	cltq
    541a:	4c 8d 0c 80          	lea    (%rax,%rax,4),%r9
    541e:	49 c1 e1 07          	shl    $0x7,%r9
    5422:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5428:	4a 8b 44 25 20       	mov    0x20(%rbp,%r12,1),%rax
    542d:	4c 89 ea             	mov    %r13,%rdx
    5430:	4a 8b 84 18 28 02 00 00 	mov    0x228(%rax,%r11,1),%rax
    5438:	4d 8d 04 02          	lea    (%r10,%rax,1),%r8
    543c:	0f 1f 40 00          	nopl   0x0(%rax)
    5440:	48 8b 0a             	mov    (%rdx),%rcx
    5443:	48 8b 70 08          	mov    0x8(%rax),%rsi
    5447:	48 83 c0 20          	add    $0x20,%rax
    544b:	48 81 c2 98 00 00 00 	add    $0x98,%rdx
    5452:	4a 8b 8c 09 28 02 00 00 	mov    0x228(%rcx,%r9,1),%rcx
    545a:	48 89 34 39          	mov    %rsi,(%rcx,%rdi,1)
    545e:	49 39 c0             	cmp    %rax,%r8
    5461:	75 dd                	jne    5440 <barriered_work+0x1f0>
    5463:	48 83 c7 20          	add    $0x20,%rdi
    5467:	49 81 c4 98 00 00 00 	add    $0x98,%r12
    546e:	4c 39 d7             	cmp    %r10,%rdi
    5471:	75 b5                	jne    5428 <barriered_work+0x1d8>
    5473:	0f ae f0             	mfence
    5476:	48 8b b3 18 02 00 00 	mov    0x218(%rbx),%rsi
    547d:	31 ff                	xor    %edi,%edi
    547f:	48 c1 e6 05          	shl    $0x5,%rsi
    5483:	48 03 b3 08 02 00 00 	add    0x208(%rbx),%rsi
    548a:	e8 61 ce ff ff       	call   22f0 <clock_gettime@plt>
    548f:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    5496:	83 bb 00 02 00 00 01 	cmpl   $0x1,0x200(%rbx)
    549d:	48 8b 42 30          	mov    0x30(%rdx),%rax
    54a1:	8b 70 10             	mov    0x10(%rax),%esi
    54a4:	8d 6e 01             	lea    0x1(%rsi),%ebp
    54a7:	89 68 10             	mov    %ebp,0x10(%rax)
    54aa:	74 0b                	je     54b7 <barriered_work+0x267>
    54ac:	eb 65                	jmp    5513 <barriered_work+0x2c3>
    54ae:	66 90                	xchg   %ax,%ax
    54b0:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    54b7:	48 63 83 30 01 00 00 	movslq 0x130(%rbx),%rax
    54be:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    54c6:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    54ca:	48 8d 04 48          	lea    (%rax,%rcx,2),%rax
    54ce:	48 8b 4a 10          	mov    0x10(%rdx),%rcx
    54d2:	48 63 13             	movslq (%rbx),%rdx
    54d5:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    54d9:	48 8d 3c 92          	lea    (%rdx,%rdx,4),%rdi
    54dd:	48 c1 e7 07          	shl    $0x7,%rdi
    54e1:	48 03 78 20          	add    0x20(%rax),%rdi
    54e5:	ff 93 20 01 00 00    	call   *0x120(%rbx)
    54eb:	0f ae f8             	sfence
    54ee:	83 bb 00 02 00 00 01 	cmpl   $0x1,0x200(%rbx)
    54f5:	74 b9                	je     54b0 <barriered_work+0x260>
    54f7:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    54fe:	48 8b 40 30          	mov    0x30(%rax),%rax
    5502:	3b 68 10             	cmp    0x10(%rax),%ebp
    5505:	74 0c                	je     5513 <barriered_work+0x2c3>
    5507:	48 8d 3d f6 0c 00 00 	lea    0xcf6(%rip),%rdi        # 6204 <_IO_stdin_used+0x204>
    550e:	e8 bd cd ff ff       	call   22d0 <puts@plt>
    5513:	48 8b b3 18 02 00 00 	mov    0x218(%rbx),%rsi
    551a:	31 ff                	xor    %edi,%edi
    551c:	48 c1 e6 05          	shl    $0x5,%rsi
    5520:	48 03 b3 08 02 00 00 	add    0x208(%rbx),%rsi
    5527:	48 83 c6 10          	add    $0x10,%rsi
    552b:	e8 c0 cd ff ff       	call   22f0 <clock_gettime@plt>
    5530:	48 8b 83 18 02 00 00 	mov    0x218(%rbx),%rax
    5537:	48 83 c0 01          	add    $0x1,%rax
    553b:	48 99                	cqto
    553d:	48 f7 bb 10 02 00 00 	idivq  0x210(%rbx)
    5544:	48 89 93 18 02 00 00 	mov    %rdx,0x218(%rbx)
    554b:	e9 55 fd ff ff       	jmp    52a5 <barriered_work+0x55>
    5550:	4c 8b bb 40 02 00 00 	mov    0x240(%rbx),%r15
    5557:	4c 89 d8             	mov    %r11,%rax
    555a:	48 d1 e8             	shr    %rax
    555d:	66 49 0f 6e c7       	movq   %r15,%xmm0
    5562:	48 c1 e0 04          	shl    $0x4,%rax
    5566:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    556a:	48 01 d0             	add    %rdx,%rax
    556d:	0f 1f 00             	nopl   (%rax)
    5570:	0f 11 02             	movups %xmm0,(%rdx)
    5573:	48 83 c2 10          	add    $0x10,%rdx
    5577:	48 39 c2             	cmp    %rax,%rdx
    557a:	75 f4                	jne    5570 <barriered_work+0x320>
    557c:	4c 89 d8             	mov    %r11,%rax
    557f:	48 83 e0 fe          	and    $0xfffffffffffffffe,%rax
    5583:	48 01 e8             	add    %rbp,%rax
    5586:	41 f6 c3 01          	test   $0x1,%r11b
    558a:	0f 84 08 fe ff ff    	je     5398 <barriered_work+0x148>
    5590:	4c 8b bb 40 02 00 00 	mov    0x240(%rbx),%r15
    5597:	4c 89 3c c7          	mov    %r15,(%rdi,%rax,8)
    559b:	e9 f8 fd ff ff       	jmp    5398 <barriered_work+0x148>
    55a0:	48 8d 04 ed 00 00 00 00 	lea    0x0(,%rbp,8),%rax
    55a8:	4a 8d 34 c5 00 00 00 00 	lea    0x0(,%r8,8),%rsi
    55b0:	e9 c0 fd ff ff       	jmp    5375 <barriered_work+0x125>
    55b5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000055c0 <barriered_work_ingest>:
    55c0:	f3 0f 1e fa          	endbr64
    55c4:	48 83 ec 08          	sub    $0x8,%rsp
    55c8:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    55cf:	48 8b 40 38          	mov    0x38(%rax),%rax
    55d3:	48 63 10             	movslq (%rax),%rdx
    55d6:	85 d2                	test   %edx,%edx
    55d8:	7e 2c                	jle    5606 <barriered_work_ingest+0x46>
    55da:	48 8b 40 08          	mov    0x8(%rax),%rax
    55de:	48 c1 e2 04          	shl    $0x4,%rdx
    55e2:	48 01 c2             	add    %rax,%rdx
    55e5:	0f 1f 00             	nopl   (%rax)
    55e8:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    55ec:	75 0f                	jne    55fd <barriered_work_ingest+0x3d>
    55ee:	48 83 87 20 02 00 00 01 	addq   $0x1,0x220(%rdi)
    55f6:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    55fd:	48 83 c0 10          	add    $0x10,%rax
    5601:	48 39 d0             	cmp    %rdx,%rax
    5604:	75 e2                	jne    55e8 <barriered_work_ingest+0x28>
    5606:	0f ae f0             	mfence
    5609:	e8 42 fc ff ff       	call   5250 <barriered_work>
    560e:	31 c0                	xor    %eax,%eax
    5610:	48 83 c4 08          	add    $0x8,%rsp
    5614:	c3                   	ret
    5615:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005620 <barriered_nulltask>:
    5620:	f3 0f 1e fa          	endbr64
    5624:	31 c0                	xor    %eax,%eax
    5626:	c3                   	ret
    5627:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005630 <barriered_steal>:
    5630:	f3 0f 1e fa          	endbr64
    5634:	31 c0                	xor    %eax,%eax
    5636:	c3                   	ret
    5637:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005640 <after>:
    5640:	f3 0f 1e fa          	endbr64
    5644:	31 c0                	xor    %eax,%eax
    5646:	48 39 d7             	cmp    %rdx,%rdi
    5649:	7e 08                	jle    5653 <after+0x13>
    564b:	31 c0                	xor    %eax,%eax
    564d:	48 39 ce             	cmp    %rcx,%rsi
    5650:	0f 9f c0             	setg   %al
    5653:	c3                   	ret
    5654:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    565f:	90                   	nop

0000000000005660 <within>:
    5660:	f3 0f 1e fa          	endbr64
    5664:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5669:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    566e:	31 c0                	xor    %eax,%eax
    5670:	48 39 d7             	cmp    %rdx,%rdi
    5673:	7f 18                	jg     568d <within+0x2d>
    5675:	4d 39 d8             	cmp    %r11,%r8
    5678:	0f 9e c2             	setle  %dl
    567b:	48 39 ce             	cmp    %rcx,%rsi
    567e:	0f 9e c0             	setle  %al
    5681:	21 c2                	and    %eax,%edx
    5683:	31 c0                	xor    %eax,%eax
    5685:	4d 39 d1             	cmp    %r10,%r9
    5688:	0f 9e c0             	setle  %al
    568b:	21 d0                	and    %edx,%eax
    568d:	c3                   	ret
    568e:	66 90                	xchg   %ax,%ax

0000000000005690 <overlap>:
    5690:	f3 0f 1e fa          	endbr64
    5694:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5699:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    569e:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    56a3:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    56a8:	4c 8b 4c 24 38       	mov    0x38(%rsp),%r9
    56ad:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
    56b2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    56b7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    56bc:	48 39 fe             	cmp    %rdi,%rsi
    56bf:	7d 2f                	jge    56f0 <overlap+0x60>
    56c1:	48 39 ca             	cmp    %rcx,%rdx
    56c4:	7d 62                	jge    5728 <overlap+0x98>
    56c6:	4d 39 da             	cmp    %r11,%r10
    56c9:	7e 0e                	jle    56d9 <overlap+0x49>
    56cb:	b8 01 00 00 00       	mov    $0x1,%eax
    56d0:	4d 39 c1             	cmp    %r8,%r9
    56d3:	0f 8f 7f 00 00 00    	jg     5758 <overlap+0xc8>
    56d9:	31 c0                	xor    %eax,%eax
    56db:	4d 39 c1             	cmp    %r8,%r9
    56de:	7c 4c                	jl     572c <overlap+0x9c>
    56e0:	31 c0                	xor    %eax,%eax
    56e2:	4d 39 da             	cmp    %r11,%r10
    56e5:	0f 9d c0             	setge  %al
    56e8:	c3                   	ret
    56e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    56f0:	7e 4e                	jle    5740 <overlap+0xb0>
    56f2:	48 39 ca             	cmp    %rcx,%rdx
    56f5:	7f 39                	jg     5730 <overlap+0xa0>
    56f7:	75 31                	jne    572a <overlap+0x9a>
    56f9:	4d 39 c1             	cmp    %r8,%r9
    56fc:	7f 2c                	jg     572a <overlap+0x9a>
    56fe:	b8 01 00 00 00       	mov    $0x1,%eax
    5703:	4d 39 da             	cmp    %r11,%r10
    5706:	7e 24                	jle    572c <overlap+0x9c>
    5708:	48 39 ca             	cmp    %rcx,%rdx
    570b:	0f 94 c2             	sete   %dl
    570e:	48 39 fe             	cmp    %rdi,%rsi
    5711:	0f 94 c0             	sete   %al
    5714:	21 c2                	and    %eax,%edx
    5716:	31 c0                	xor    %eax,%eax
    5718:	4d 39 c1             	cmp    %r8,%r9
    571b:	0f 94 c0             	sete   %al
    571e:	21 d0                	and    %edx,%eax
    5720:	c3                   	ret
    5721:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5728:	74 af                	je     56d9 <overlap+0x49>
    572a:	31 c0                	xor    %eax,%eax
    572c:	c3                   	ret
    572d:	0f 1f 00             	nopl   (%rax)
    5730:	4d 39 c1             	cmp    %r8,%r9
    5733:	7d c4                	jge    56f9 <overlap+0x69>
    5735:	b8 01 00 00 00       	mov    $0x1,%eax
    573a:	4d 39 da             	cmp    %r11,%r10
    573d:	7d ba                	jge    56f9 <overlap+0x69>
    573f:	c3                   	ret
    5740:	48 39 ca             	cmp    %rcx,%rdx
    5743:	7c 94                	jl     56d9 <overlap+0x49>
    5745:	4d 39 c1             	cmp    %r8,%r9
    5748:	7e b4                	jle    56fe <overlap+0x6e>
    574a:	48 39 ca             	cmp    %rcx,%rdx
    574d:	74 91                	je     56e0 <overlap+0x50>
    574f:	eb d9                	jmp    572a <overlap+0x9a>
    5751:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5758:	c3                   	ret
    5759:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005760 <verify>:
    5760:	f3 0f 1e fa          	endbr64
    5764:	85 f6                	test   %esi,%esi
    5766:	0f 8e 2d 03 00 00    	jle    5a99 <verify+0x339>
    576c:	41 57                	push   %r15
    576e:	41 89 f7             	mov    %esi,%r15d
    5771:	41 56                	push   %r14
    5773:	45 31 f6             	xor    %r14d,%r14d
    5776:	41 55                	push   %r13
    5778:	41 54                	push   %r12
    577a:	55                   	push   %rbp
    577b:	53                   	push   %rbx
    577c:	48 8d 5f 20          	lea    0x20(%rdi),%rbx
    5780:	48 83 ec 48          	sub    $0x48,%rsp
    5784:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    5789:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    578e:	31 ed                	xor    %ebp,%ebp
    5790:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    5795:	41 89 ec             	mov    %ebp,%r12d
    5798:	45 39 f4             	cmp    %r14d,%r12d
    579b:	0f 84 4b 02 00 00    	je     59ec <verify+0x28c>
    57a1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    57a6:	8b 50 08             	mov    0x8(%rax),%edx
    57a9:	85 d2                	test   %edx,%edx
    57ab:	0f 8e 3b 02 00 00    	jle    59ec <verify+0x28c>
    57b1:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
    57b9:	45 31 ed             	xor    %r13d,%r13d
    57bc:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    57c1:	44 89 f2             	mov    %r14d,%edx
    57c4:	48 8d 35 49 0a 00 00 	lea    0xa49(%rip),%rsi        # 6214 <_IO_stdin_used+0x214>
    57cb:	bf 01 00 00 00       	mov    $0x1,%edi
    57d0:	31 c0                	xor    %eax,%eax
    57d2:	e8 59 cc ff ff       	call   2430 <__printf_chk@plt>
    57d7:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    57dc:	8b 40 08             	mov    0x8(%rax),%eax
    57df:	85 c0                	test   %eax,%eax
    57e1:	0f 8e e5 01 00 00    	jle    59cc <verify+0x26c>
    57e7:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    57ec:	44 89 6c 24 34       	mov    %r13d,0x34(%rsp)
    57f1:	31 db                	xor    %ebx,%ebx
    57f3:	44 89 74 24 38       	mov    %r14d,0x38(%rsp)
    57f8:	44 89 7c 24 3c       	mov    %r15d,0x3c(%rsp)
    57fd:	48 8b 28             	mov    (%rax),%rbp
    5800:	4c 8b 6c 24 08       	mov    0x8(%rsp),%r13
    5805:	48 8d 04 9b          	lea    (%rbx,%rbx,4),%rax
    5809:	4c 8b 3c 24          	mov    (%rsp),%r15
    580d:	48 8d 35 15 0a 00 00 	lea    0xa15(%rip),%rsi        # 6229 <_IO_stdin_used+0x229>
    5814:	49 89 c6             	mov    %rax,%r14
    5817:	bf 01 00 00 00       	mov    $0x1,%edi
    581c:	49 8b 45 00          	mov    0x0(%r13),%rax
    5820:	49 c1 e6 07          	shl    $0x7,%r14
    5824:	4a 8b 8c 3d 18 02 00 00 	mov    0x218(%rbp,%r15,1),%rcx
    582c:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    5831:	4a 8b 94 30 18 02 00 00 	mov    0x218(%rax,%r14,1),%rdx
    5839:	31 c0                	xor    %eax,%eax
    583b:	e8 f0 cb ff ff       	call   2430 <__printf_chk@plt>
    5840:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5845:	48 8b 28             	mov    (%rax),%rbp
    5848:	4a 83 bc 3d 18 02 00 00 00 	cmpq   $0x0,0x218(%rbp,%r15,1)
    5851:	0f 8e 54 01 00 00    	jle    59ab <verify+0x24b>
    5857:	4d 03 75 00          	add    0x0(%r13),%r14
    585b:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
    5860:	ba 01 00 00 00       	mov    $0x1,%edx
    5865:	4d 89 f3             	mov    %r14,%r11
    5868:	4d 8b b3 18 02 00 00 	mov    0x218(%r11),%r14
    586f:	4d 85 f6             	test   %r14,%r14
    5872:	0f 8e 2e 01 00 00    	jle    59a6 <verify+0x246>
    5878:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5880:	48 8b 04 24          	mov    (%rsp),%rax
    5884:	49 89 d4             	mov    %rdx,%r12
    5887:	31 db                	xor    %ebx,%ebx
    5889:	49 89 d5             	mov    %rdx,%r13
    588c:	49 c1 e4 05          	shl    $0x5,%r12
    5890:	49 83 ec 20          	sub    $0x20,%r12
    5894:	4c 8d 7c 05 00       	lea    0x0(%rbp,%rax,1),%r15
    5899:	eb 32                	jmp    58cd <verify+0x16d>
    589b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    58a0:	4c 39 c2             	cmp    %r8,%rdx
    58a3:	0f 8d 67 01 00 00    	jge    5a10 <verify+0x2b0>
    58a9:	4c 39 d7             	cmp    %r10,%rdi
    58ac:	7e 09                	jle    58b7 <verify+0x157>
    58ae:	49 39 c1             	cmp    %rax,%r9
    58b1:	0f 8c 81 00 00 00    	jl     5938 <verify+0x1d8>
    58b7:	4c 39 d7             	cmp    %r10,%rdi
    58ba:	0f 8d 9b 01 00 00    	jge    5a5b <verify+0x2fb>
    58c0:	48 83 c3 01          	add    $0x1,%rbx
    58c4:	49 39 de             	cmp    %rbx,%r14
    58c7:	0f 8e b9 00 00 00    	jle    5986 <verify+0x226>
    58cd:	49 8b 97 08 02 00 00 	mov    0x208(%r15),%rdx
    58d4:	48 89 d8             	mov    %rbx,%rax
    58d7:	48 c1 e0 05          	shl    $0x5,%rax
    58db:	49 03 83 08 02 00 00 	add    0x208(%r11),%rax
    58e2:	4c 01 e2             	add    %r12,%rdx
    58e5:	48 8b 08             	mov    (%rax),%rcx
    58e8:	48 8b 78 10          	mov    0x10(%rax),%rdi
    58ec:	48 8b 32             	mov    (%rdx),%rsi
    58ef:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    58f3:	4c 8b 52 10          	mov    0x10(%rdx),%r10
    58f7:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    58fb:	48 8b 50 08          	mov    0x8(%rax),%rdx
    58ff:	48 8b 40 18          	mov    0x18(%rax),%rax
    5903:	48 39 f1             	cmp    %rsi,%rcx
    5906:	7c 98                	jl     58a0 <verify+0x140>
    5908:	0f 8e 32 01 00 00    	jle    5a40 <verify+0x2e0>
    590e:	4c 39 c2             	cmp    %r8,%rdx
    5911:	0f 8f 09 01 00 00    	jg     5a20 <verify+0x2c0>
    5917:	75 a7                	jne    58c0 <verify+0x160>
    5919:	4c 39 d7             	cmp    %r10,%rdi
    591c:	7f a2                	jg     58c0 <verify+0x160>
    591e:	49 39 c1             	cmp    %rax,%r9
    5921:	7d 15                	jge    5938 <verify+0x1d8>
    5923:	48 39 f1             	cmp    %rsi,%rcx
    5926:	75 98                	jne    58c0 <verify+0x160>
    5928:	4c 39 c2             	cmp    %r8,%rdx
    592b:	75 93                	jne    58c0 <verify+0x160>
    592d:	4c 39 d7             	cmp    %r10,%rdi
    5930:	75 8e                	jne    58c0 <verify+0x160>
    5932:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5938:	49 89 c1             	mov    %rax,%r9
    593b:	48 89 f9             	mov    %rdi,%rcx
    593e:	48 89 f2             	mov    %rsi,%rdx
    5941:	bf 01 00 00 00       	mov    $0x1,%edi
    5946:	48 8d 35 53 0b 00 00 	lea    0xb53(%rip),%rsi        # 64a0 <_IO_stdin_used+0x4a0>
    594d:	31 c0                	xor    %eax,%eax
    594f:	48 83 c3 01          	add    $0x1,%rbx
    5953:	e8 d8 ca ff ff       	call   2430 <__printf_chk@plt>
    5958:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    595d:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    5962:	4c 03 18             	add    (%rax),%r11
    5965:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    596a:	4d 8b b3 18 02 00 00 	mov    0x218(%r11),%r14
    5971:	48 8b 28             	mov    (%rax),%rbp
    5974:	48 8b 04 24          	mov    (%rsp),%rax
    5978:	4c 8d 7c 05 00       	lea    0x0(%rbp,%rax,1),%r15
    597d:	49 39 de             	cmp    %rbx,%r14
    5980:	0f 8f 47 ff ff ff    	jg     58cd <verify+0x16d>
    5986:	4c 89 ea             	mov    %r13,%rdx
    5989:	4d 3b af 18 02 00 00 	cmp    0x218(%r15),%r13
    5990:	7d 14                	jge    59a6 <verify+0x246>
    5992:	4d 8b b3 18 02 00 00 	mov    0x218(%r11),%r14
    5999:	48 83 c2 01          	add    $0x1,%rdx
    599d:	4d 85 f6             	test   %r14,%r14
    59a0:	0f 8f da fe ff ff    	jg     5880 <verify+0x120>
    59a6:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    59ab:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    59b0:	48 83 c3 01          	add    $0x1,%rbx
    59b4:	39 58 08             	cmp    %ebx,0x8(%rax)
    59b7:	0f 8f 43 fe ff ff    	jg     5800 <verify+0xa0>
    59bd:	44 8b 6c 24 34       	mov    0x34(%rsp),%r13d
    59c2:	44 8b 74 24 38       	mov    0x38(%rsp),%r14d
    59c7:	44 8b 7c 24 3c       	mov    0x3c(%rsp),%r15d
    59cc:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    59d1:	48 81 04 24 80 02 00 00 	addq   $0x280,(%rsp)
    59d9:	41 83 c5 01          	add    $0x1,%r13d
    59dd:	44 39 68 08          	cmp    %r13d,0x8(%rax)
    59e1:	0f 8f da fd ff ff    	jg     57c1 <verify+0x61>
    59e7:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    59ec:	48 81 44 24 08 98 00 00 00 	addq   $0x98,0x8(%rsp)
    59f5:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    59fa:	41 39 c7             	cmp    %eax,%r15d
    59fd:	74 6a                	je     5a69 <verify+0x309>
    59ff:	41 89 c4             	mov    %eax,%r12d
    5a02:	e9 91 fd ff ff       	jmp    5798 <verify+0x38>
    5a07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    5a10:	0f 85 aa fe ff ff    	jne    58c0 <verify+0x160>
    5a16:	e9 9c fe ff ff       	jmp    58b7 <verify+0x157>
    5a1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5a20:	4c 39 d7             	cmp    %r10,%rdi
    5a23:	0f 8d f0 fe ff ff    	jge    5919 <verify+0x1b9>
    5a29:	49 39 c1             	cmp    %rax,%r9
    5a2c:	0f 8e e7 fe ff ff    	jle    5919 <verify+0x1b9>
    5a32:	e9 01 ff ff ff       	jmp    5938 <verify+0x1d8>
    5a37:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    5a40:	4c 39 c2             	cmp    %r8,%rdx
    5a43:	0f 8c 6e fe ff ff    	jl     58b7 <verify+0x157>
    5a49:	4c 39 d7             	cmp    %r10,%rdi
    5a4c:	0f 8e cc fe ff ff    	jle    591e <verify+0x1be>
    5a52:	4c 39 c2             	cmp    %r8,%rdx
    5a55:	0f 85 65 fe ff ff    	jne    58c0 <verify+0x160>
    5a5b:	49 39 c1             	cmp    %rax,%r9
    5a5e:	0f 8f 5c fe ff ff    	jg     58c0 <verify+0x160>
    5a64:	e9 cf fe ff ff       	jmp    5938 <verify+0x1d8>
    5a69:	48 81 44 24 10 98 00 00 00 	addq   $0x98,0x10(%rsp)
    5a72:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    5a77:	41 8d 46 01          	lea    0x1(%r14),%eax
    5a7b:	45 39 f4             	cmp    %r14d,%r12d
    5a7e:	74 08                	je     5a88 <verify+0x328>
    5a80:	41 89 c6             	mov    %eax,%r14d
    5a83:	e9 01 fd ff ff       	jmp    5789 <verify+0x29>
    5a88:	48 83 c4 48          	add    $0x48,%rsp
    5a8c:	31 c0                	xor    %eax,%eax
    5a8e:	5b                   	pop    %rbx
    5a8f:	5d                   	pop    %rbp
    5a90:	41 5c                	pop    %r12
    5a92:	41 5d                	pop    %r13
    5a94:	41 5e                	pop    %r14
    5a96:	41 5f                	pop    %r15
    5a98:	c3                   	ret
    5a99:	31 c0                	xor    %eax,%eax
    5a9b:	c3                   	ret

Disassembly of section .fini:

0000000000005a9c <_fini>:
    5a9c:	f3 0f 1e fa          	endbr64
    5aa0:	48 83 ec 08          	sub    $0x8,%rsp
    5aa4:	48 83 c4 08          	add    $0x8,%rsp
    5aa8:	c3                   	ret
