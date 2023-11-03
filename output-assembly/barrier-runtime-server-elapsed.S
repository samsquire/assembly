
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
    261c:	ba 0f 27 00 00       	mov    $0x270f,%edx
    2621:	48 8d 35 00 3f 00 00 	lea    0x3f00(%rip),%rsi        # 6528 <_IO_stdin_used+0x528>
    2628:	31 c0                	xor    %eax,%eax
    262a:	bf 01 00 00 00       	mov    $0x1,%edi
    262f:	e8 fc fd ff ff       	call   2430 <__printf_chk@plt>
    2634:	ba 0f 27 00 00       	mov    $0x270f,%edx
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
    26c4:	bf 0f 27 00 00       	mov    $0x270f,%edi
    26c9:	c7 00 0f 27 00 00    	movl   $0x270f,(%rax)
    26cf:	48 89 c3             	mov    %rax,%rbx
    26d2:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    26d7:	e8 a4 fc ff ff       	call   2380 <calloc@plt>
    26dc:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    26e1:	48 89 43 08          	mov    %rax,0x8(%rbx)
    26e5:	48 8d 90 f0 70 02 00 	lea    0x270f0(%rax),%rdx
    26ec:	0f 1f 40 00          	nopl   0x0(%rax)
    26f0:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    26f7:	48 83 c0 10          	add    $0x10,%rax
    26fb:	48 39 c2             	cmp    %rax,%rdx
    26fe:	75 f0                	jne    26f0 <main+0x190>
    2700:	c7 44 24 30 00 00 00 00 	movl   $0x0,0x30(%rsp)
    2708:	4d 89 d7             	mov    %r10,%r15
    270b:	31 c9                	xor    %ecx,%ecx
    270d:	4c 89 54 24 48       	mov    %r10,0x48(%rsp)
    2712:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    2718:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    271d:	41 89 0f             	mov    %ecx,(%r15)
    2720:	be 10 00 00 00       	mov    $0x10,%esi
    2725:	31 db                	xor    %ebx,%ebx
    2727:	41 c7 47 28 07 00 00 00 	movl   $0x7,0x28(%r15)
    272f:	bf 64 00 00 00       	mov    $0x64,%edi
    2734:	49 89 47 10          	mov    %rax,0x10(%r15)
    2738:	48 8b 05 a9 42 00 00 	mov    0x42a9(%rip),%rax        # 69e8 <_IO_stdin_used+0x9e8>
    273f:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    2743:	49 89 47 18          	mov    %rax,0x18(%r15)
    2747:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    274c:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    2751:	49 89 47 30          	mov    %rax,0x30(%r15)
    2755:	e8 26 fc ff ff       	call   2380 <calloc@plt>
    275a:	be 10 00 00 00       	mov    $0x10,%esi
    275f:	bf 64 00 00 00       	mov    $0x64,%edi
    2764:	49 89 47 50          	mov    %rax,0x50(%r15)
    2768:	e8 13 fc ff ff       	call   2380 <calloc@plt>
    276d:	be 28 00 00 00       	mov    $0x28,%esi
    2772:	bf 64 00 00 00       	mov    $0x64,%edi
    2777:	66 0f 6f 05 51 42 00 00 	movdqa 0x4251(%rip),%xmm0        # 69d0 <_IO_stdin_used+0x9d0>
    277f:	49 89 47 58          	mov    %rax,0x58(%r15)
    2783:	41 0f 11 47 68       	movups %xmm0,0x68(%r15)
    2788:	e8 f3 fb ff ff       	call   2380 <calloc@plt>
    278d:	be 98 00 00 00       	mov    $0x98,%esi
    2792:	bf 07 00 00 00       	mov    $0x7,%edi
    2797:	66 0f 6f 0d 31 42 00 00 	movdqa 0x4231(%rip),%xmm1        # 69d0 <_IO_stdin_used+0x9d0>
    279f:	49 89 47 78          	mov    %rax,0x78(%r15)
    27a3:	41 0f 11 8f 80 00 00 00 	movups %xmm1,0x80(%r15)
    27ab:	e8 d0 fb ff ff       	call   2380 <calloc@plt>
    27b0:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
    27b5:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
    27ba:	49 89 47 20          	mov    %rax,0x20(%r15)
    27be:	48 89 c2             	mov    %rax,%rdx
    27c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    27c8:	4c 63 eb             	movslq %ebx,%r13
    27cb:	44 89 74 24 20       	mov    %r14d,0x20(%rsp)
    27d0:	4b 8d 44 ed 00       	lea    0x0(%r13,%r13,8),%rax
    27d5:	4d 8d 64 45 00       	lea    0x0(%r13,%rax,2),%r12
    27da:	49 c1 e4 03          	shl    $0x3,%r12
    27de:	4a 8d 2c 22          	lea    (%rdx,%r12,1),%rbp
    27e2:	41 39 de             	cmp    %ebx,%r14d
    27e5:	0f 84 35 0a 00 00    	je     3220 <main+0xcc0>
    27eb:	be 20 00 00 00       	mov    $0x20,%esi
    27f0:	bf 06 00 00 00       	mov    $0x6,%edi
    27f5:	e8 86 fb ff ff       	call   2380 <calloc@plt>
    27fa:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    27fe:	4c 89 64 24 18       	mov    %r12,0x18(%rsp)
    2803:	49 89 c7             	mov    %rax,%r15
    2806:	48 89 45 70          	mov    %rax,0x70(%rbp)
    280a:	48 8d a8 c0 00 00 00 	lea    0xc0(%rax),%rbp
    2811:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    2818:	be 08 00 00 00       	mov    $0x8,%esi
    281d:	bf 0f 27 00 00       	mov    $0x270f,%edi
    2822:	49 83 c7 20          	add    $0x20,%r15
    2826:	e8 55 fb ff ff       	call   2380 <calloc@plt>
    282b:	be 08 00 00 00       	mov    $0x8,%esi
    2830:	bf 0f 27 00 00       	mov    $0x270f,%edi
    2835:	49 89 c4             	mov    %rax,%r12
    2838:	e8 43 fb ff ff       	call   2380 <calloc@plt>
    283d:	be 18 00 00 00       	mov    $0x18,%esi
    2842:	bf 02 00 00 00       	mov    $0x2,%edi
    2847:	48 89 c3             	mov    %rax,%rbx
    284a:	e8 31 fb ff ff       	call   2380 <calloc@plt>
    284f:	48 8d 70 18          	lea    0x18(%rax),%rsi
    2853:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    285b:	49 89 47 e0          	mov    %rax,-0x20(%r15)
    285f:	49 89 77 e8          	mov    %rsi,-0x18(%r15)
    2863:	4c 89 20             	mov    %r12,(%rax)
    2866:	48 89 58 18          	mov    %rbx,0x18(%rax)
    286a:	48 c7 40 10 0f 27 00 00 	movq   $0x270f,0x10(%rax)
    2872:	48 c7 40 20 00 00 00 00 	movq   $0x0,0x20(%rax)
    287a:	48 c7 40 28 0f 27 00 00 	movq   $0x270f,0x28(%rax)
    2882:	4c 39 fd             	cmp    %r15,%rbp
    2885:	75 91                	jne    2818 <main+0x2b8>
    2887:	be 01 00 00 00       	mov    $0x1,%esi
    288c:	bf 00 01 00 00       	mov    $0x100,%edi
    2891:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    2895:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    289a:	e8 e1 fa ff ff       	call   2380 <calloc@plt>
    289f:	bf 18 00 00 00       	mov    $0x18,%edi
    28a4:	48 89 c5             	mov    %rax,%rbp
    28a7:	e8 44 fb ff ff       	call   23f0 <malloc@plt>
    28ac:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    28b1:	48 89 ef             	mov    %rbp,%rdi
    28b4:	41 89 d9             	mov    %ebx,%r9d
    28b7:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    28bc:	48 8d 0d bd 3c 00 00 	lea    0x3cbd(%rip),%rcx        # 6580 <_IO_stdin_used+0x580>
    28c3:	ba 00 01 00 00       	mov    $0x100,%edx
    28c8:	31 c0                	xor    %eax,%eax
    28ca:	be 01 00 00 00       	mov    $0x1,%esi
    28cf:	e8 2c fc ff ff       	call   2500 <__sprintf_chk@plt>
    28d4:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    28d9:	8d 43 01             	lea    0x1(%rbx),%eax
    28dc:	b9 ab aa aa aa       	mov    $0xaaaaaaab,%ecx
    28e1:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    28e6:	be 20 00 00 00       	mov    $0x20,%esi
    28eb:	49 89 2a             	mov    %rbp,(%r10)
    28ee:	48 89 c5             	mov    %rax,%rbp
    28f1:	48 0f af c1          	imul   %rcx,%rax
    28f5:	49 8b 57 20          	mov    0x20(%r15),%rdx
    28f9:	4d 89 6a 10          	mov    %r13,0x10(%r10)
    28fd:	4d 89 72 08          	mov    %r14,0x8(%r10)
    2901:	48 c1 e8 22          	shr    $0x22,%rax
    2905:	4e 8d 2c 22          	lea    (%rdx,%r12,1),%r13
    2909:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
    290e:	8d 0c 40             	lea    (%rax,%rax,2),%ecx
    2911:	89 e8                	mov    %ebp,%eax
    2913:	01 c9                	add    %ecx,%ecx
    2915:	29 c8                	sub    %ecx,%eax
    2917:	41 89 85 90 00 00 00 	mov    %eax,0x90(%r13)
    291e:	4d 89 95 88 00 00 00 	mov    %r10,0x88(%r13)
    2925:	41 c7 85 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%r13)
    2930:	49 c7 45 58 3f 42 0f 00 	movq   $0xf423f,0x58(%r13)
    2938:	49 8b 7d 58          	mov    0x58(%r13),%rdi
    293c:	e8 3f fa ff ff       	call   2380 <calloc@plt>
    2941:	83 fb 05             	cmp    $0x5,%ebx
    2944:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    2949:	49 89 45 50          	mov    %rax,0x50(%r13)
    294d:	8b 44 24 08          	mov    0x8(%rsp),%eax
    2951:	49 c7 45 60 00 00 00 00 	movq   $0x0,0x60(%r13)
    2959:	41 89 45 38          	mov    %eax,0x38(%r13)
    295d:	4d 89 7d 30          	mov    %r15,0x30(%r13)
    2961:	41 c7 45 40 01 00 00 00 	movl   $0x1,0x40(%r13)
    2969:	41 c7 45 08 00 00 00 00 	movl   $0x0,0x8(%r13)
    2971:	41 c7 45 3c 06 00 00 00 	movl   $0x6,0x3c(%r13)
    2979:	41 c7 45 44 07 00 00 00 	movl   $0x7,0x44(%r13)
    2981:	41 c7 85 84 00 00 00 06 00 00 00 	movl   $0x6,0x84(%r13)
    298c:	41 89 5d 00          	mov    %ebx,0x0(%r13)
    2990:	0f 84 9a 08 00 00    	je     3230 <main+0xcd0>
    2996:	39 5c 24 20          	cmp    %ebx,0x20(%rsp)
    299a:	0f 85 70 08 00 00    	jne    3210 <main+0xcb0>
    29a0:	8b 4c 24 30          	mov    0x30(%rsp),%ecx
    29a4:	85 c9                	test   %ecx,%ecx
    29a6:	0f 85 64 08 00 00    	jne    3210 <main+0xcb0>
    29ac:	89 c2                	mov    %eax,%edx
    29ae:	48 8d 35 f3 3b 00 00 	lea    0x3bf3(%rip),%rsi        # 65a8 <_IO_stdin_used+0x5a8>
    29b5:	bf 01 00 00 00       	mov    $0x1,%edi
    29ba:	31 c0                	xor    %eax,%eax
    29bc:	e8 6f fa ff ff       	call   2430 <__printf_chk@plt>
    29c1:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    29c6:	48 8b 4c 24 38       	mov    0x38(%rsp),%rcx
    29cb:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    29d3:	48 8b 50 20          	mov    0x20(%rax),%rdx
    29d7:	48 89 48 38          	mov    %rcx,0x38(%rax)
    29db:	48 8d 05 ce 2a 00 00 	lea    0x2ace(%rip),%rax        # 54b0 <barriered_work_ingest>
    29e2:	49 01 d4             	add    %rdx,%r12
    29e5:	49 89 44 24 20       	mov    %rax,0x20(%r12)
    29ea:	83 fd 07             	cmp    $0x7,%ebp
    29ed:	74 11                	je     2a00 <main+0x4a0>
    29ef:	89 eb                	mov    %ebp,%ebx
    29f1:	e9 d2 fd ff ff       	jmp    27c8 <main+0x268>
    29f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    2a00:	48 8d 05 79 09 00 00 	lea    0x979(%rip),%rax        # 3380 <barriered_reset>
    2a07:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    2a0c:	4c 89 f1             	mov    %r14,%rcx
    2a0f:	48 89 82 b0 03 00 00 	mov    %rax,0x3b0(%rdx)
    2a16:	8b 44 24 08          	mov    0x8(%rsp),%eax
    2a1a:	48 83 c1 01          	add    $0x1,%rcx
    2a1e:	4c 89 ba c0 03 00 00 	mov    %r15,0x3c0(%rdx)
    2a25:	49 81 c7 98 00 00 00 	add    $0x98,%r15
    2a2c:	c7 82 d0 03 00 00 01 00 00 00 	movl   $0x1,0x3d0(%rdx)
    2a36:	c7 82 98 03 00 00 00 00 00 00 	movl   $0x0,0x398(%rdx)
    2a40:	c7 82 90 03 00 00 06 00 00 00 	movl   $0x6,0x390(%rdx)
    2a4a:	c7 82 cc 03 00 00 06 00 00 00 	movl   $0x6,0x3cc(%rdx)
    2a54:	89 82 c8 03 00 00    	mov    %eax,0x3c8(%rdx)
    2a5a:	c7 82 14 04 00 00 06 00 00 00 	movl   $0x6,0x414(%rdx)
    2a64:	c7 82 d4 03 00 00 07 00 00 00 	movl   $0x7,0x3d4(%rdx)
    2a6e:	48 83 f9 09          	cmp    $0x9,%rcx
    2a72:	0f 85 a0 fc ff ff    	jne    2718 <main+0x1b8>
    2a78:	4c 8b 54 24 48       	mov    0x48(%rsp),%r10
    2a7d:	be 38 00 00 00       	mov    $0x38,%esi
    2a82:	bf 09 00 00 00       	mov    $0x9,%edi
    2a87:	45 31 ed             	xor    %r13d,%r13d
    2a8a:	4c 8d 3d 5f 09 00 00 	lea    0x95f(%rip),%r15        # 33f0 <barriered_thread>
    2a91:	49 8d 82 28 04 00 00 	lea    0x428(%r10),%rax
    2a98:	4c 89 54 24 20       	mov    %r10,0x20(%rsp)
    2a9d:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2aa2:	49 8b 42 20          	mov    0x20(%r10),%rax
    2aa6:	4d 89 92 38 04 00 00 	mov    %r10,0x438(%r10)
    2aad:	41 c7 82 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r10)
    2ab8:	41 c7 82 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r10)
    2ac3:	41 c7 82 50 04 00 00 07 00 00 00 	movl   $0x7,0x450(%r10)
    2ace:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2ad5:	49 8b 82 b8 00 00 00 	mov    0xb8(%r10),%rax
    2adc:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2ae3:	49 8b 82 50 01 00 00 	mov    0x150(%r10),%rax
    2aea:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2af1:	49 8b 82 e8 01 00 00 	mov    0x1e8(%r10),%rax
    2af8:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2aff:	49 8b 82 80 02 00 00 	mov    0x280(%r10),%rax
    2b06:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2b0d:	49 8b 82 18 03 00 00 	mov    0x318(%r10),%rax
    2b14:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
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
    2b5a:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    2b5f:	ba 06 00 00 00       	mov    $0x6,%edx
    2b64:	48 8d 35 84 37 00 00 	lea    0x3784(%rip),%rsi        # 62ef <_IO_stdin_used+0x2ef>
    2b6b:	49 89 c4             	mov    %rax,%r12
    2b6e:	bf 01 00 00 00       	mov    $0x1,%edi
    2b73:	31 c0                	xor    %eax,%eax
    2b75:	41 c7 82 94 03 00 00 00 00 00 00 	movl   $0x0,0x394(%r10)
    2b80:	4c 89 e5             	mov    %r12,%rbp
    2b83:	41 c7 82 bc 03 00 00 01 00 00 00 	movl   $0x1,0x3bc(%r10)
    2b8e:	41 c7 82 b8 03 00 00 07 00 00 00 	movl   $0x7,0x3b8(%r10)
    2b99:	4d 89 92 a0 03 00 00 	mov    %r10,0x3a0(%r10)
    2ba0:	41 c7 82 a8 03 00 00 06 00 00 00 	movl   $0x6,0x3a8(%r10)
    2bab:	41 c7 82 90 03 00 00 00 00 00 00 	movl   $0x0,0x390(%r10)
    2bb6:	e8 75 f8 ff ff       	call   2430 <__printf_chk@plt>
    2bbb:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    2bc0:	49 8d 7c 24 30       	lea    0x30(%r12),%rdi
    2bc5:	45 89 ec             	mov    %r13d,%r12d
    2bc8:	48 8d b3 50 01 00 00 	lea    0x150(%rbx),%rsi
    2bcf:	48 8d 15 5a 0b 00 00 	lea    0xb5a(%rip),%rdx        # 3730 <timer_thread>
    2bd6:	49 89 ed             	mov    %rbp,%r13
    2bd9:	49 8d 8a 90 03 00 00 	lea    0x390(%r10),%rcx
    2be0:	e8 6b f8 ff ff       	call   2450 <pthread_create@plt>
    2be5:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
    2bea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    2bf0:	41 c7 46 04 01 00 00 00 	movl   $0x1,0x4(%r14)
    2bf8:	44 89 e2             	mov    %r12d,%edx
    2bfb:	bf 01 00 00 00       	mov    $0x1,%edi
    2c00:	31 c0                	xor    %eax,%eax
    2c02:	41 c7 46 2c 01 00 00 00 	movl   $0x1,0x2c(%r14)
    2c0a:	48 8d 35 b7 39 00 00 	lea    0x39b7(%rip),%rsi        # 65c8 <_IO_stdin_used+0x5c8>
    2c11:	41 83 c4 01          	add    $0x1,%r12d
    2c15:	e8 16 f8 ff ff       	call   2430 <__printf_chk@plt>
    2c1a:	4c 89 f1             	mov    %r14,%rcx
    2c1d:	48 89 de             	mov    %rbx,%rsi
    2c20:	48 89 ef             	mov    %rbp,%rdi
    2c23:	4c 89 fa             	mov    %r15,%rdx
    2c26:	49 81 c6 98 00 00 00 	add    $0x98,%r14
    2c2d:	48 83 c5 08          	add    $0x8,%rbp
    2c31:	48 83 c3 38          	add    $0x38,%rbx
    2c35:	e8 16 f8 ff ff       	call   2450 <pthread_create@plt>
    2c3a:	41 83 fc 06          	cmp    $0x6,%r12d
    2c3e:	75 b0                	jne    2bf0 <main+0x690>
    2c40:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    2c45:	be d8 00 00 00       	mov    $0xd8,%esi
    2c4a:	4d 89 ec             	mov    %r13,%r12
    2c4d:	31 db                	xor    %ebx,%ebx
    2c4f:	bf 01 00 00 00       	mov    $0x1,%edi
    2c54:	48 8d 2d 04 37 00 00 	lea    0x3704(%rip),%rbp        # 635f <_IO_stdin_used+0x35f>
    2c5b:	41 c7 82 2c 04 00 00 02 00 00 00 	movl   $0x2,0x42c(%r10)
    2c66:	41 c7 82 54 04 00 00 01 00 00 00 	movl   $0x1,0x454(%r10)
    2c71:	41 c7 82 50 04 00 00 00 00 00 00 	movl   $0x0,0x450(%r10)
    2c7c:	e8 ff f6 ff ff       	call   2380 <calloc@plt>
    2c81:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    2c86:	be 00 08 00 00       	mov    $0x800,%esi
    2c8b:	31 ff                	xor    %edi,%edi
    2c8d:	49 89 82 68 04 00 00 	mov    %rax,0x468(%r10)
    2c94:	e8 f7 f7 ff ff       	call   2490 <eventfd@plt>
    2c99:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    2c9e:	ba 07 00 00 00       	mov    $0x7,%edx
    2ca3:	48 8d 35 63 36 00 00 	lea    0x3663(%rip),%rsi        # 630d <_IO_stdin_used+0x30d>
    2caa:	bf 01 00 00 00       	mov    $0x1,%edi
    2caf:	41 89 82 70 04 00 00 	mov    %eax,0x470(%r10)
    2cb6:	31 c0                	xor    %eax,%eax
    2cb8:	4d 89 92 38 04 00 00 	mov    %r10,0x438(%r10)
    2cbf:	41 c7 82 40 04 00 00 06 00 00 00 	movl   $0x6,0x440(%r10)
    2cca:	41 c7 82 28 04 00 00 07 00 00 00 	movl   $0x7,0x428(%r10)
    2cd5:	e8 56 f7 ff ff       	call   2430 <__printf_chk@plt>
    2cda:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    2cdf:	49 8d 7d 38          	lea    0x38(%r13),%rdi
    2ce3:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    2ce8:	48 8d 15 01 1d 00 00 	lea    0x1d01(%rip),%rdx        # 49f0 <io_thread>
    2cef:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    2cf6:	e8 55 f7 ff ff       	call   2450 <pthread_create@plt>
    2cfb:	ba 08 00 00 00       	mov    $0x8,%edx
    2d00:	48 8d 35 1d 36 00 00 	lea    0x361d(%rip),%rsi        # 6324 <_IO_stdin_used+0x324>
    2d07:	31 c0                	xor    %eax,%eax
    2d09:	bf 01 00 00 00       	mov    $0x1,%edi
    2d0e:	e8 1d f7 ff ff       	call   2430 <__printf_chk@plt>
    2d13:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    2d18:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    2d1d:	49 8d 7d 40          	lea    0x40(%r13),%rdi
    2d21:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    2d26:	48 8d 15 43 09 00 00 	lea    0x943(%rip),%rdx        # 3670 <external_thread>
    2d2d:	4c 8d 6c 24 50       	lea    0x50(%rsp),%r13
    2d32:	49 89 82 f8 04 00 00 	mov    %rax,0x4f8(%r10)
    2d39:	48 8b 05 a8 3c 00 00 	mov    0x3ca8(%rip),%rax        # 69e8 <_IO_stdin_used+0x9e8>
    2d40:	49 8d 8a c0 04 00 00 	lea    0x4c0(%r10),%rcx
    2d47:	4d 89 92 d0 04 00 00 	mov    %r10,0x4d0(%r10)
    2d4e:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
    2d55:	41 c7 82 c4 04 00 00 03 00 00 00 	movl   $0x3,0x4c4(%r10)
    2d60:	41 c7 82 ec 04 00 00 01 00 00 00 	movl   $0x1,0x4ec(%r10)
    2d6b:	41 c7 82 e8 04 00 00 00 00 00 00 	movl   $0x0,0x4e8(%r10)
    2d76:	49 89 82 d8 04 00 00 	mov    %rax,0x4d8(%r10)
    2d7d:	41 c7 82 c0 04 00 00 08 00 00 00 	movl   $0x8,0x4c0(%r10)
    2d88:	4c 89 54 24 08       	mov    %r10,0x8(%rsp)
    2d8d:	e8 be f6 ff ff       	call   2450 <pthread_create@plt>
    2d92:	48 8d 3d a8 35 00 00 	lea    0x35a8(%rip),%rdi        # 6341 <_IO_stdin_used+0x341>
    2d99:	e8 32 f5 ff ff       	call   22d0 <puts@plt>
    2d9e:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    2da3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    2da8:	49 8b 3c dc          	mov    (%r12,%rbx,8),%rdi
    2dac:	4c 89 ee             	mov    %r13,%rsi
    2daf:	e8 1c f7 ff ff       	call   24d0 <pthread_join@plt>
    2db4:	89 da                	mov    %ebx,%edx
    2db6:	48 89 ee             	mov    %rbp,%rsi
    2db9:	bf 01 00 00 00       	mov    $0x1,%edi
    2dbe:	31 c0                	xor    %eax,%eax
    2dc0:	48 83 c3 01          	add    $0x1,%rbx
    2dc4:	e8 67 f6 ff ff       	call   2430 <__printf_chk@plt>
    2dc9:	48 83 fb 09          	cmp    $0x9,%rbx
    2dcd:	75 d9                	jne    2da8 <main+0x848>
    2dcf:	49 8d 86 b0 03 00 00 	lea    0x3b0(%r14),%rax
    2dd6:	31 ed                	xor    %ebp,%ebp
    2dd8:	31 c9                	xor    %ecx,%ecx
    2dda:	45 31 c9             	xor    %r9d,%r9d
    2ddd:	45 31 c0             	xor    %r8d,%r8d
    2de0:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    2de5:	45 31 e4             	xor    %r12d,%r12d
    2de8:	4d 8d 6e 20          	lea    0x20(%r14),%r13
    2dec:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2df1:	31 db                	xor    %ebx,%ebx
    2df3:	4c 89 44 24 10       	mov    %r8,0x10(%rsp)
    2df8:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    2dfd:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    2e02:	4c 89 74 24 30       	mov    %r14,0x30(%rsp)
    2e07:	4d 89 e6             	mov    %r12,%r14
    2e0a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    2e10:	49 63 55 08          	movslq 0x8(%r13),%rdx
    2e14:	85 d2                	test   %edx,%edx
    2e16:	0f 8e cf 00 00 00    	jle    2eeb <main+0x98b>
    2e1c:	49 8b 45 00          	mov    0x0(%r13),%rax
    2e20:	48 8d 34 d2          	lea    (%rdx,%rdx,8),%rsi
    2e24:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    2e29:	48 8d 14 72          	lea    (%rdx,%rsi,2),%rdx
    2e2d:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    2e32:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    2e37:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    2e3c:	48 8d 14 d0          	lea    (%rax,%rdx,8),%rdx
    2e40:	48 8b 70 10          	mov    0x10(%rax),%rsi
    2e44:	48 05 98 00 00 00    	add    $0x98,%rax
    2e4a:	49 01 f6             	add    %rsi,%r14
    2e4d:	48 8b 70 80          	mov    -0x80(%rax),%rsi
    2e51:	48 01 f1             	add    %rsi,%rcx
    2e54:	48 8b 70 d0          	mov    -0x30(%rax),%rsi
    2e58:	49 01 f3             	add    %rsi,%r11
    2e5b:	48 8b 70 e0          	mov    -0x20(%rax),%rsi
    2e5f:	49 01 f1             	add    %rsi,%r9
    2e62:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2e66:	48 03 6e 10          	add    0x10(%rsi),%rbp
    2e6a:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2e6e:	48 03 5e 18          	add    0x18(%rsi),%rbx
    2e72:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2e76:	48 03 6e 30          	add    0x30(%rsi),%rbp
    2e7a:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2e7e:	48 03 5e 38          	add    0x38(%rsi),%rbx
    2e82:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2e86:	48 03 6e 50          	add    0x50(%rsi),%rbp
    2e8a:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2e8e:	48 03 5e 58          	add    0x58(%rsi),%rbx
    2e92:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2e96:	48 03 6e 70          	add    0x70(%rsi),%rbp
    2e9a:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2e9e:	48 03 5e 78          	add    0x78(%rsi),%rbx
    2ea2:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2ea6:	48 03 ae 90 00 00 00 	add    0x90(%rsi),%rbp
    2ead:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2eb1:	48 03 9e 98 00 00 00 	add    0x98(%rsi),%rbx
    2eb8:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2ebc:	48 03 ae b0 00 00 00 	add    0xb0(%rsi),%rbp
    2ec3:	48 8b 70 d8          	mov    -0x28(%rax),%rsi
    2ec7:	48 03 9e b8 00 00 00 	add    0xb8(%rsi),%rbx
    2ece:	48 39 d0             	cmp    %rdx,%rax
    2ed1:	0f 85 69 ff ff ff    	jne    2e40 <main+0x8e0>
    2ed7:	4c 89 5c 24 08       	mov    %r11,0x8(%rsp)
    2edc:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    2ee1:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    2ee6:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    2eeb:	45 31 e4             	xor    %r12d,%r12d
    2eee:	49 83 7d 50 00       	cmpq   $0x0,0x50(%r13)
    2ef3:	7e 79                	jle    2f6e <main+0xa0e>
    2ef5:	4c 89 ed             	mov    %r13,%rbp
    2ef8:	49 89 dd             	mov    %rbx,%r13
    2efb:	4c 89 e3             	mov    %r12,%rbx
    2efe:	66 90                	xchg   %ax,%ax
    2f00:	48 8b 7d 30          	mov    0x30(%rbp),%rdi
    2f04:	48 89 de             	mov    %rbx,%rsi
    2f07:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
    2f11:	48 83 c3 01          	add    $0x1,%rbx
    2f15:	48 c1 e6 04          	shl    $0x4,%rsi
    2f19:	48 01 f7             	add    %rsi,%rdi
    2f1c:	48 03 75 38          	add    0x38(%rbp),%rsi
    2f20:	48 8b 56 08          	mov    0x8(%rsi),%rdx
    2f24:	48 2b 57 08          	sub    0x8(%rdi),%rdx
    2f28:	48 f7 e2             	mul    %rdx
    2f2b:	31 c0                	xor    %eax,%eax
    2f2d:	48 89 d1             	mov    %rdx,%rcx
    2f30:	48 8b 16             	mov    (%rsi),%rdx
    2f33:	48 8d 35 39 34 00 00 	lea    0x3439(%rip),%rsi        # 6373 <_IO_stdin_used+0x373>
    2f3a:	48 2b 17             	sub    (%rdi),%rdx
    2f3d:	48 c1 e9 12          	shr    $0x12,%rcx
    2f41:	bf 01 00 00 00       	mov    $0x1,%edi
    2f46:	e8 e5 f4 ff ff       	call   2430 <__printf_chk@plt>
    2f4b:	48 8b 55 40          	mov    0x40(%rbp),%rdx
    2f4f:	bf 01 00 00 00       	mov    $0x1,%edi
    2f54:	31 c0                	xor    %eax,%eax
    2f56:	48 8d 35 34 34 00 00 	lea    0x3434(%rip),%rsi        # 6391 <_IO_stdin_used+0x391>
    2f5d:	e8 ce f4 ff ff       	call   2430 <__printf_chk@plt>
    2f62:	48 39 5d 50          	cmp    %rbx,0x50(%rbp)
    2f66:	7f 98                	jg     2f00 <main+0x9a0>
    2f68:	4c 89 eb             	mov    %r13,%rbx
    2f6b:	49 89 ed             	mov    %rbp,%r13
    2f6e:	49 bf ab aa aa aa aa aa aa aa 	movabs $0xaaaaaaaaaaaaaaab,%r15
    2f78:	45 31 e4             	xor    %r12d,%r12d
    2f7b:	49 83 7d 68 00       	cmpq   $0x0,0x68(%r13)
    2f80:	0f 8e 95 00 00 00    	jle    301b <main+0xabb>
    2f86:	48 89 d8             	mov    %rbx,%rax
    2f89:	4c 89 e5             	mov    %r12,%rbp
    2f8c:	4c 89 eb             	mov    %r13,%rbx
    2f8f:	49 89 c5             	mov    %rax,%r13
    2f92:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    2f98:	48 8b 43 58          	mov    0x58(%rbx),%rax
    2f9c:	48 8d 54 ad 00       	lea    0x0(%rbp,%rbp,4),%rdx
    2fa1:	48 83 ec 08          	sub    $0x8,%rsp
    2fa5:	48 8d 35 44 36 00 00 	lea    0x3644(%rip),%rsi        # 65f0 <_IO_stdin_used+0x5f0>
    2fac:	bf 01 00 00 00       	mov    $0x1,%edi
    2fb1:	48 83 c5 01          	add    $0x1,%rbp
    2fb5:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    2fb9:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
    2fc3:	4c 8b 61 18          	mov    0x18(%rcx),%r12
    2fc7:	4c 2b 61 08          	sub    0x8(%rcx),%r12
    2fcb:	49 f7 e4             	mul    %r12
    2fce:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    2fd2:	4c 2b 01             	sub    (%rcx),%r8
    2fd5:	31 c0                	xor    %eax,%eax
    2fd7:	8b 49 20             	mov    0x20(%rcx),%ecx
    2fda:	41 54                	push   %r12
    2fdc:	48 c1 ea 12          	shr    $0x12,%rdx
    2fe0:	49 89 d1             	mov    %rdx,%r9
    2fe3:	ba 06 00 00 00       	mov    $0x6,%edx
    2fe8:	e8 43 f4 ff ff       	call   2430 <__printf_chk@plt>
    2fed:	4c 89 e0             	mov    %r12,%rax
    2ff0:	bf 01 00 00 00       	mov    $0x1,%edi
    2ff5:	48 8d 35 b1 33 00 00 	lea    0x33b1(%rip),%rsi        # 63ad <_IO_stdin_used+0x3ad>
    2ffc:	49 f7 e7             	mul    %r15
    2fff:	31 c0                	xor    %eax,%eax
    3001:	48 c1 ea 02          	shr    $0x2,%rdx
    3005:	e8 26 f4 ff ff       	call   2430 <__printf_chk@plt>
    300a:	58                   	pop    %rax
    300b:	5a                   	pop    %rdx
    300c:	48 39 6b 68          	cmp    %rbp,0x68(%rbx)
    3010:	7f 86                	jg     2f98 <main+0xa38>
    3012:	4c 89 e8             	mov    %r13,%rax
    3015:	49 89 dd             	mov    %rbx,%r13
    3018:	48 89 c3             	mov    %rax,%rbx
    301b:	49 8b 55 70          	mov    0x70(%r13),%rdx
    301f:	48 8d 35 7b 33 00 00 	lea    0x337b(%rip),%rsi        # 63a1 <_IO_stdin_used+0x3a1>
    3026:	bf 01 00 00 00       	mov    $0x1,%edi
    302b:	31 c0                	xor    %eax,%eax
    302d:	49 81 c5 98 00 00 00 	add    $0x98,%r13
    3034:	e8 f7 f3 ff ff       	call   2430 <__printf_chk@plt>
    3039:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    303e:	49 39 c5             	cmp    %rax,%r13
    3041:	0f 85 c9 fd ff ff    	jne    2e10 <main+0x8b0>
    3047:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
    304c:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    3051:	4c 89 f2             	mov    %r14,%rdx
    3054:	31 c0                	xor    %eax,%eax
    3056:	48 8d 35 62 33 00 00 	lea    0x3362(%rip),%rsi        # 63bf <_IO_stdin_used+0x3bf>
    305d:	bf 01 00 00 00       	mov    $0x1,%edi
    3062:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    3067:	4d 89 f4             	mov    %r14,%r12
    306a:	49 bd 89 88 88 88 88 88 88 88 	movabs $0x8888888888888889,%r13
    3074:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    3079:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    307e:	e8 ad f3 ff ff       	call   2430 <__printf_chk@plt>
    3083:	bf 0a 00 00 00       	mov    $0xa,%edi
    3088:	e8 33 f2 ff ff       	call   22c0 <putchar@plt>
    308d:	4c 8b 74 24 40       	mov    0x40(%rsp),%r14
    3092:	48 8d 35 3a 33 00 00 	lea    0x333a(%rip),%rsi        # 63d3 <_IO_stdin_used+0x3d3>
    3099:	31 c0                	xor    %eax,%eax
    309b:	bf 01 00 00 00       	mov    $0x1,%edi
    30a0:	49 8b 16             	mov    (%r14),%rdx
    30a3:	e8 88 f3 ff ff       	call   2430 <__printf_chk@plt>
    30a8:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    30ad:	48 8d 35 34 33 00 00 	lea    0x3334(%rip),%rsi        # 63e8 <_IO_stdin_used+0x3e8>
    30b4:	31 c0                	xor    %eax,%eax
    30b6:	bf 01 00 00 00       	mov    $0x1,%edi
    30bb:	e8 70 f3 ff ff       	call   2430 <__printf_chk@plt>
    30c0:	bf 0a 00 00 00       	mov    $0xa,%edi
    30c5:	e8 f6 f1 ff ff       	call   22c0 <putchar@plt>
    30ca:	49 8b 36             	mov    (%r14),%rsi
    30cd:	bf 01 00 00 00       	mov    $0x1,%edi
    30d2:	48 89 f0             	mov    %rsi,%rax
    30d5:	49 f7 ed             	imul   %r13
    30d8:	31 c0                	xor    %eax,%eax
    30da:	48 01 f2             	add    %rsi,%rdx
    30dd:	48 c1 fe 3f          	sar    $0x3f,%rsi
    30e1:	48 c1 fa 04          	sar    $0x4,%rdx
    30e5:	48 29 f2             	sub    %rsi,%rdx
    30e8:	48 8d 35 39 35 00 00 	lea    0x3539(%rip),%rsi        # 6628 <_IO_stdin_used+0x628>
    30ef:	e8 3c f3 ff ff       	call   2430 <__printf_chk@plt>
    30f4:	49 8b 56 08          	mov    0x8(%r14),%rdx
    30f8:	bf 01 00 00 00       	mov    $0x1,%edi
    30fd:	31 c0                	xor    %eax,%eax
    30ff:	48 8d 35 42 35 00 00 	lea    0x3542(%rip),%rsi        # 6648 <_IO_stdin_used+0x648>
    3106:	e8 25 f3 ff ff       	call   2430 <__printf_chk@plt>
    310b:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    3110:	bf 01 00 00 00       	mov    $0x1,%edi
    3115:	48 8d 35 54 35 00 00 	lea    0x3554(%rip),%rsi        # 6670 <_IO_stdin_used+0x670>
    311c:	4c 89 c8             	mov    %r9,%rax
    311f:	49 f7 ed             	imul   %r13
    3122:	31 c0                	xor    %eax,%eax
    3124:	4c 01 ca             	add    %r9,%rdx
    3127:	49 c1 f9 3f          	sar    $0x3f,%r9
    312b:	48 c1 fa 04          	sar    $0x4,%rdx
    312f:	4c 29 ca             	sub    %r9,%rdx
    3132:	e8 f9 f2 ff ff       	call   2430 <__printf_chk@plt>
    3137:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    313c:	bf 01 00 00 00       	mov    $0x1,%edi
    3141:	48 8d 35 58 35 00 00 	lea    0x3558(%rip),%rsi        # 66a0 <_IO_stdin_used+0x6a0>
    3148:	48 89 c8             	mov    %rcx,%rax
    314b:	49 f7 ed             	imul   %r13
    314e:	31 c0                	xor    %eax,%eax
    3150:	48 01 ca             	add    %rcx,%rdx
    3153:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3157:	48 c1 fa 04          	sar    $0x4,%rdx
    315b:	48 29 ca             	sub    %rcx,%rdx
    315e:	e8 cd f2 ff ff       	call   2430 <__printf_chk@plt>
    3163:	4c 89 e0             	mov    %r12,%rax
    3166:	bf 01 00 00 00       	mov    $0x1,%edi
    316b:	48 8d 35 5e 35 00 00 	lea    0x355e(%rip),%rsi        # 66d0 <_IO_stdin_used+0x6d0>
    3172:	49 f7 ed             	imul   %r13
    3175:	4c 01 e2             	add    %r12,%rdx
    3178:	49 c1 fc 3f          	sar    $0x3f,%r12
    317c:	31 c0                	xor    %eax,%eax
    317e:	48 c1 fa 04          	sar    $0x4,%rdx
    3182:	4c 29 e2             	sub    %r12,%rdx
    3185:	e8 a6 f2 ff ff       	call   2430 <__printf_chk@plt>
    318a:	48 89 e8             	mov    %rbp,%rax
    318d:	bf 01 00 00 00       	mov    $0x1,%edi
    3192:	48 8d 35 5c 32 00 00 	lea    0x325c(%rip),%rsi        # 63f5 <_IO_stdin_used+0x3f5>
    3199:	49 f7 ed             	imul   %r13
    319c:	31 c0                	xor    %eax,%eax
    319e:	48 01 ea             	add    %rbp,%rdx
    31a1:	48 c1 fd 3f          	sar    $0x3f,%rbp
    31a5:	48 c1 fa 04          	sar    $0x4,%rdx
    31a9:	48 29 ea             	sub    %rbp,%rdx
    31ac:	e8 7f f2 ff ff       	call   2430 <__printf_chk@plt>
    31b1:	48 89 d8             	mov    %rbx,%rax
    31b4:	bf 01 00 00 00       	mov    $0x1,%edi
    31b9:	48 8d 35 46 32 00 00 	lea    0x3246(%rip),%rsi        # 6406 <_IO_stdin_used+0x406>
    31c0:	49 f7 ed             	imul   %r13
    31c3:	31 c0                	xor    %eax,%eax
    31c5:	48 01 da             	add    %rbx,%rdx
    31c8:	48 c1 fb 3f          	sar    $0x3f,%rbx
    31cc:	48 c1 fa 04          	sar    $0x4,%rdx
    31d0:	48 29 da             	sub    %rbx,%rdx
    31d3:	e8 58 f2 ff ff       	call   2430 <__printf_chk@plt>
    31d8:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    31dd:	be 06 00 00 00       	mov    $0x6,%esi
    31e2:	e8 89 24 00 00       	call   5670 <verify>
    31e7:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    31ec:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    31f5:	75 50                	jne    3247 <main+0xce7>
    31f7:	48 83 c4 68          	add    $0x68,%rsp
    31fb:	31 c0                	xor    %eax,%eax
    31fd:	5b                   	pop    %rbx
    31fe:	5d                   	pop    %rbp
    31ff:	41 5c                	pop    %r12
    3201:	41 5d                	pop    %r13
    3203:	41 5e                	pop    %r14
    3205:	41 5f                	pop    %r15
    3207:	c3                   	ret
    3208:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3210:	48 8d 05 09 20 00 00 	lea    0x2009(%rip),%rax        # 5220 <barriered_work>
    3217:	49 89 45 20          	mov    %rax,0x20(%r13)
    321b:	e9 ca f7 ff ff       	jmp    29ea <main+0x48a>
    3220:	48 8d 05 19 01 00 00 	lea    0x119(%rip),%rax        # 3340 <do_protected_write>
    3227:	48 89 45 28          	mov    %rax,0x28(%rbp)
    322b:	e9 bb f5 ff ff       	jmp    27eb <main+0x28b>
    3230:	48 8d 05 e9 1f 00 00 	lea    0x1fe9(%rip),%rax        # 5220 <barriered_work>
    3237:	bd 06 00 00 00       	mov    $0x6,%ebp
    323c:	49 89 45 20          	mov    %rax,0x20(%r13)
    3240:	89 eb                	mov    %ebp,%ebx
    3242:	e9 81 f5 ff ff       	jmp    27c8 <main+0x268>
    3247:	e8 c4 f0 ff ff       	call   2310 <__stack_chk_fail@plt>
    324c:	0f 1f 40 00          	nopl   0x0(%rax)

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
    3268:	48 8d 3d f1 f2 ff ff 	lea    -0xd0f(%rip),%rdi        # 2560 <main>
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
    3344:	48 8b 47 30          	mov    0x30(%rdi),%rax
    3348:	48 8b 57 18          	mov    0x18(%rdi),%rdx
    334c:	48 8b 40 30          	mov    0x30(%rax),%rax
    3350:	48 83 c2 01          	add    $0x1,%rdx
    3354:	48 89 57 18          	mov    %rdx,0x18(%rdi)
    3358:	48 8b 48 08          	mov    0x8(%rax),%rcx
    335c:	48 83 00 01          	addq   $0x1,(%rax)
    3360:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    3367:	48 85 c9             	test   %rcx,%rcx
    336a:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    3371:	48 0f 4f d6          	cmovg  %rsi,%rdx
    3375:	48 89 50 08          	mov    %rdx,0x8(%rax)
    3379:	31 c0                	xor    %eax,%eax
    337b:	c3                   	ret
    337c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003380 <barriered_reset>:
    3380:	f3 0f 1e fa          	endbr64
    3384:	8b 47 44             	mov    0x44(%rdi),%eax
    3387:	48 89 fa             	mov    %rdi,%rdx
    338a:	85 c0                	test   %eax,%eax
    338c:	7e 55                	jle    33e3 <barriered_reset+0x63>
    338e:	31 c9                	xor    %ecx,%ecx
    3390:	31 f6                	xor    %esi,%esi
    3392:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3398:	48 8b 7a 30          	mov    0x30(%rdx),%rdi
    339c:	48 63 42 38          	movslq 0x38(%rdx),%rax
    33a0:	83 c6 01             	add    $0x1,%esi
    33a3:	4c 8d 04 c0          	lea    (%rax,%rax,8),%r8
    33a7:	4a 8d 04 40          	lea    (%rax,%r8,2),%rax
    33ab:	4c 8b 47 10          	mov    0x10(%rdi),%r8
    33af:	49 8d 04 c0          	lea    (%r8,%rax,8),%rax
    33b3:	48 8b 78 20          	mov    0x20(%rax),%rdi
    33b7:	48 01 cf             	add    %rcx,%rdi
    33ba:	8b 47 08             	mov    0x8(%rdi),%eax
    33bd:	83 c0 01             	add    $0x1,%eax
    33c0:	89 47 08             	mov    %eax,0x8(%rdi)
    33c3:	48 8b 42 30          	mov    0x30(%rdx),%rax
    33c7:	48 8b 78 20          	mov    0x20(%rax),%rdi
    33cb:	48 01 cf             	add    %rcx,%rdi
    33ce:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    33d5:	c7 47 40 01 00 00 00 	movl   $0x1,0x40(%rdi)
    33dc:	8b 42 44             	mov    0x44(%rdx),%eax
    33df:	39 f0                	cmp    %esi,%eax
    33e1:	7f b5                	jg     3398 <barriered_reset+0x18>
    33e3:	0f ae f0             	mfence
    33e6:	31 c0                	xor    %eax,%eax
    33e8:	c3                   	ret
    33e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000033f0 <barriered_thread>:
    33f0:	f3 0f 1e fa          	endbr64
    33f4:	8b 47 2c             	mov    0x2c(%rdi),%eax
    33f7:	83 f8 01             	cmp    $0x1,%eax
    33fa:	0f 85 60 02 00 00    	jne    3660 <barriered_thread+0x270>
    3400:	41 55                	push   %r13
    3402:	45 31 ed             	xor    %r13d,%r13d
    3405:	41 54                	push   %r12
    3407:	49 89 fc             	mov    %rdi,%r12
    340a:	55                   	push   %rbp
    340b:	53                   	push   %rbx
    340c:	31 db                	xor    %ebx,%ebx
    340e:	48 83 ec 08          	sub    $0x8,%rsp
    3412:	44 8b 57 28          	mov    0x28(%rdi),%r10d
    3416:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3420:	44 39 d3             	cmp    %r10d,%ebx
    3423:	7c 14                	jl     3439 <barriered_thread+0x49>
    3425:	49 83 84 24 90 00 00 00 01 	addq   $0x1,0x90(%r12)
    342e:	31 db                	xor    %ebx,%ebx
    3430:	45 85 d2             	test   %r10d,%r10d
    3433:	0f 8e 67 01 00 00    	jle    35a0 <barriered_thread+0x1b0>
    3439:	48 63 c3             	movslq %ebx,%rax
    343c:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3440:	48 8d 2c 50          	lea    (%rax,%rdx,2),%rbp
    3444:	48 c1 e5 03          	shl    $0x3,%rbp
    3448:	eb 19                	jmp    3463 <barriered_thread+0x73>
    344a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3450:	83 c3 01             	add    $0x1,%ebx
    3453:	48 81 c5 98 00 00 00 	add    $0x98,%rbp
    345a:	44 39 d3             	cmp    %r10d,%ebx
    345d:	0f 8d 3d 01 00 00    	jge    35a0 <barriered_thread+0x1b0>
    3463:	49 8b 54 24 20       	mov    0x20(%r12),%rdx
    3468:	48 01 ea             	add    %rbp,%rdx
    346b:	8b 42 40             	mov    0x40(%rdx),%eax
    346e:	83 f8 01             	cmp    $0x1,%eax
    3471:	75 dd                	jne    3450 <barriered_thread+0x60>
    3473:	85 db                	test   %ebx,%ebx
    3475:	0f 8e 45 01 00 00    	jle    35c0 <barriered_thread+0x1d0>
    347b:	45 8b 5c 24 18       	mov    0x18(%r12),%r11d
    3480:	8d 43 ff             	lea    -0x1(%rbx),%eax
    3483:	45 85 db             	test   %r11d,%r11d
    3486:	7e 6d                	jle    34f5 <barriered_thread+0x105>
    3488:	48 98                	cltq
    348a:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    348e:	4c 8d 04 48          	lea    (%rax,%rcx,2),%r8
    3492:	49 63 cb             	movslq %r11d,%rcx
    3495:	49 8b 44 24 10       	mov    0x10(%r12),%rax
    349a:	48 8d 34 c9          	lea    (%rcx,%rcx,8),%rsi
    349e:	49 c1 e0 03          	shl    $0x3,%r8
    34a2:	48 8d 0c 71          	lea    (%rcx,%rsi,2),%rcx
    34a6:	4c 8d 0c c8          	lea    (%rax,%rcx,8),%r9
    34aa:	31 c9                	xor    %ecx,%ecx
    34ac:	0f 1f 40 00          	nopl   0x0(%rax)
    34b0:	48 8b 70 20          	mov    0x20(%rax),%rsi
    34b4:	4c 01 c6             	add    %r8,%rsi
    34b7:	8b 76 08             	mov    0x8(%rsi),%esi
    34ba:	8b 7a 08             	mov    0x8(%rdx),%edi
    34bd:	39 f7                	cmp    %esi,%edi
    34bf:	40 0f 94 c6          	sete   %sil
    34c3:	48 05 98 00 00 00    	add    $0x98,%rax
    34c9:	40 0f b6 f6          	movzbl %sil,%esi
    34cd:	01 f1                	add    %esi,%ecx
    34cf:	4c 39 c8             	cmp    %r9,%rax
    34d2:	75 dc                	jne    34b0 <barriered_thread+0xc0>
    34d4:	44 39 d9             	cmp    %r11d,%ecx
    34d7:	74 08                	je     34e1 <barriered_thread+0xf1>
    34d9:	85 c9                	test   %ecx,%ecx
    34db:	0f 85 bf 00 00 00    	jne    35a0 <barriered_thread+0x1b0>
    34e1:	85 db                	test   %ebx,%ebx
    34e3:	75 10                	jne    34f5 <barriered_thread+0x105>
    34e5:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
    34ea:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
    34ef:	0f 8c 53 01 00 00    	jl     3648 <barriered_thread+0x258>
    34f5:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    34fd:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    3501:	49 8b 44 24 78       	mov    0x78(%r12),%rax
    3506:	41 83 fd 01          	cmp    $0x1,%r13d
    350a:	0f 84 00 01 00 00    	je     3610 <barriered_thread+0x220>
    3510:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    3514:	bf 04 00 00 00       	mov    $0x4,%edi
    3519:	41 bd 01 00 00 00    	mov    $0x1,%r13d
    351f:	89 5e 20             	mov    %ebx,0x20(%rsi)
    3522:	e8 c9 ed ff ff       	call   22f0 <clock_gettime@plt>
    3527:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    352c:	48 01 e8             	add    %rbp,%rax
    352f:	c7 40 40 00 00 00 00 	movl   $0x0,0x40(%rax)
    3536:	48 8b 50 20          	mov    0x20(%rax),%rdx
    353a:	49 63 04 24          	movslq (%r12),%rax
    353e:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    3542:	48 8d 04 48          	lea    (%rax,%rcx,2),%rax
    3546:	49 8b 4c 24 10       	mov    0x10(%r12),%rcx
    354b:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    354f:	48 8b 78 20          	mov    0x20(%rax),%rdi
    3553:	48 01 ef             	add    %rbp,%rdi
    3556:	ff d2                	call   *%rdx
    3558:	49 8b 54 24 20       	mov    0x20(%r12),%rdx
    355d:	48 01 ea             	add    %rbp,%rdx
    3560:	8b 42 08             	mov    0x8(%rdx),%eax
    3563:	83 c0 01             	add    $0x1,%eax
    3566:	89 42 08             	mov    %eax,0x8(%rdx)
    3569:	41 8b 44 24 28       	mov    0x28(%r12),%eax
    356e:	49 83 44 24 60 01    	addq   $0x1,0x60(%r12)
    3574:	83 e8 01             	sub    $0x1,%eax
    3577:	39 d8                	cmp    %ebx,%eax
    3579:	74 65                	je     35e0 <barriered_thread+0x1f0>
    357b:	0f ae f0             	mfence
    357e:	45 8b 54 24 28       	mov    0x28(%r12),%r10d
    3583:	83 c3 01             	add    $0x1,%ebx
    3586:	48 81 c5 98 00 00 00 	add    $0x98,%rbp
    358d:	44 39 d3             	cmp    %r10d,%ebx
    3590:	0f 8c cd fe ff ff    	jl     3463 <barriered_thread+0x73>
    3596:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    35a0:	41 8b 44 24 2c       	mov    0x2c(%r12),%eax
    35a5:	83 f8 01             	cmp    $0x1,%eax
    35a8:	0f 84 72 fe ff ff    	je     3420 <barriered_thread+0x30>
    35ae:	48 83 c4 08          	add    $0x8,%rsp
    35b2:	31 c0                	xor    %eax,%eax
    35b4:	5b                   	pop    %rbx
    35b5:	5d                   	pop    %rbp
    35b6:	41 5c                	pop    %r12
    35b8:	41 5d                	pop    %r13
    35ba:	c3                   	ret
    35bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    35c0:	45 8b 5c 24 18       	mov    0x18(%r12),%r11d
    35c5:	41 8d 42 ff          	lea    -0x1(%r10),%eax
    35c9:	45 85 db             	test   %r11d,%r11d
    35cc:	0f 8f b6 fe ff ff    	jg     3488 <barriered_thread+0x98>
    35d2:	e9 0a ff ff ff       	jmp    34e1 <barriered_thread+0xf1>
    35d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    35e0:	49 8b 74 24 68       	mov    0x68(%r12),%rsi
    35e5:	49 3b 74 24 70       	cmp    0x70(%r12),%rsi
    35ea:	7d 8f                	jge    357b <barriered_thread+0x18b>
    35ec:	48 c1 e6 04          	shl    $0x4,%rsi
    35f0:	bf 04 00 00 00       	mov    $0x4,%edi
    35f5:	49 03 74 24 58       	add    0x58(%r12),%rsi
    35fa:	e8 f1 ec ff ff       	call   22f0 <clock_gettime@plt>
    35ff:	49 83 44 24 68 01    	addq   $0x1,0x68(%r12)
    3605:	e9 71 ff ff ff       	jmp    357b <barriered_thread+0x18b>
    360a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3610:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    3615:	bf 04 00 00 00       	mov    $0x4,%edi
    361a:	45 31 ed             	xor    %r13d,%r13d
    361d:	e8 ce ec ff ff       	call   22f0 <clock_gettime@plt>
    3622:	49 8b 84 24 80 00 00 00 	mov    0x80(%r12),%rax
    362a:	48 83 c0 01          	add    $0x1,%rax
    362e:	48 99                	cqto
    3630:	49 f7 bc 24 88 00 00 00 	idivq  0x88(%r12)
    3638:	49 89 94 24 80 00 00 00 	mov    %rdx,0x80(%r12)
    3640:	e9 e2 fe ff ff       	jmp    3527 <barriered_thread+0x137>
    3645:	0f 1f 00             	nopl   (%rax)
    3648:	48 c1 e6 04          	shl    $0x4,%rsi
    364c:	bf 04 00 00 00       	mov    $0x4,%edi
    3651:	49 03 74 24 50       	add    0x50(%r12),%rsi
    3656:	e8 95 ec ff ff       	call   22f0 <clock_gettime@plt>
    365b:	e9 95 fe ff ff       	jmp    34f5 <barriered_thread+0x105>
    3660:	31 c0                	xor    %eax,%eax
    3662:	c3                   	ret
    3663:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    366e:	66 90                	xchg   %ax,%ax

0000000000003670 <external_thread>:
    3670:	f3 0f 1e fa          	endbr64
    3674:	41 55                	push   %r13
    3676:	41 54                	push   %r12
    3678:	55                   	push   %rbp
    3679:	53                   	push   %rbx
    367a:	48 83 ec 38          	sub    $0x38,%rsp
    367e:	66 0f 6f 05 6a 32 00 00 	movdqa 0x326a(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
    3686:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    368f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3694:	31 c0                	xor    %eax,%eax
    3696:	0f 29 04 24          	movaps %xmm0,(%rsp)
    369a:	8b 47 2c             	mov    0x2c(%rdi),%eax
    369d:	83 f8 01             	cmp    $0x1,%eax
    36a0:	75 64                	jne    3706 <external_thread+0x96>
    36a2:	49 89 fd             	mov    %rdi,%r13
    36a5:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    36aa:	48 89 e3             	mov    %rsp,%rbx
    36ad:	4c 8d 25 50 29 00 00 	lea    0x2950(%rip),%r12        # 6004 <_IO_stdin_used+0x4>
    36b4:	0f 1f 40 00          	nopl   0x0(%rax)
    36b8:	48 89 ee             	mov    %rbp,%rsi
    36bb:	48 89 df             	mov    %rbx,%rdi
    36be:	e8 6d ec ff ff       	call   2330 <nanosleep@plt>
    36c3:	49 8b 45 38          	mov    0x38(%r13),%rax
    36c7:	48 63 08             	movslq (%rax),%rcx
    36ca:	85 c9                	test   %ecx,%ecx
    36cc:	7e 2c                	jle    36fa <external_thread+0x8a>
    36ce:	48 8b 40 08          	mov    0x8(%rax),%rax
    36d2:	48 c1 e1 04          	shl    $0x4,%rcx
    36d6:	48 01 c1             	add    %rax,%rcx
    36d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    36e0:	8b 50 08             	mov    0x8(%rax),%edx
    36e3:	85 d2                	test   %edx,%edx
    36e5:	75 0a                	jne    36f1 <external_thread+0x81>
    36e7:	4c 89 20             	mov    %r12,(%rax)
    36ea:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    36f1:	48 83 c0 10          	add    $0x10,%rax
    36f5:	48 39 c1             	cmp    %rax,%rcx
    36f8:	75 e6                	jne    36e0 <external_thread+0x70>
    36fa:	0f ae f0             	mfence
    36fd:	41 8b 45 2c          	mov    0x2c(%r13),%eax
    3701:	83 f8 01             	cmp    $0x1,%eax
    3704:	74 b2                	je     36b8 <external_thread+0x48>
    3706:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    370b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3714:	75 0d                	jne    3723 <external_thread+0xb3>
    3716:	48 83 c4 38          	add    $0x38,%rsp
    371a:	31 c0                	xor    %eax,%eax
    371c:	5b                   	pop    %rbx
    371d:	5d                   	pop    %rbp
    371e:	41 5c                	pop    %r12
    3720:	41 5d                	pop    %r13
    3722:	c3                   	ret
    3723:	e8 e8 eb ff ff       	call   2310 <__stack_chk_fail@plt>
    3728:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000003730 <timer_thread>:
    3730:	f3 0f 1e fa          	endbr64
    3734:	41 57                	push   %r15
    3736:	48 8d 35 d3 28 00 00 	lea    0x28d3(%rip),%rsi        # 6010 <_IO_stdin_used+0x10>
    373d:	49 89 ff             	mov    %rdi,%r15
    3740:	41 56                	push   %r14
    3742:	41 55                	push   %r13
    3744:	41 54                	push   %r12
    3746:	55                   	push   %rbp
    3747:	53                   	push   %rbx
    3748:	48 83 ec 58          	sub    $0x58,%rsp
    374c:	8b 17                	mov    (%rdi),%edx
    374e:	bf 01 00 00 00       	mov    $0x1,%edi
    3753:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    375c:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3761:	31 c0                	xor    %eax,%eax
    3763:	e8 c8 ec ff ff       	call   2430 <__printf_chk@plt>
    3768:	66 0f 6f 05 80 31 00 00 	movdqa 0x3180(%rip),%xmm0        # 68f0 <_IO_stdin_used+0x8f0>
    3770:	ba 30 75 00 00       	mov    $0x7530,%edx
    3775:	31 c0                	xor    %eax,%eax
    3777:	48 8d 35 a4 28 00 00 	lea    0x28a4(%rip),%rsi        # 6022 <_IO_stdin_used+0x22>
    377e:	bf 01 00 00 00       	mov    $0x1,%edi
    3783:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3788:	e8 a3 ec ff ff       	call   2430 <__printf_chk@plt>
    378d:	4d 63 77 2c          	movslq 0x2c(%r15),%r14
    3791:	45 85 f6             	test   %r14d,%r14d
    3794:	0f 84 a9 00 00 00    	je     3843 <timer_thread+0x113>
    379a:	45 31 ed             	xor    %r13d,%r13d
    379d:	45 31 f6             	xor    %r14d,%r14d
    37a0:	49 89 e4             	mov    %rsp,%r12
    37a3:	31 db                	xor    %ebx,%ebx
    37a5:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    37aa:	48 89 ef             	mov    %rbp,%rdi
    37ad:	4c 89 e6             	mov    %r12,%rsi
    37b0:	41 83 c5 01          	add    $0x1,%r13d
    37b4:	e8 77 eb ff ff       	call   2330 <nanosleep@plt>
    37b9:	49 63 47 18          	movslq 0x18(%r15),%rax
    37bd:	41 8d 7e 01          	lea    0x1(%r14),%edi
    37c1:	85 c0                	test   %eax,%eax
    37c3:	7e 59                	jle    381e <timer_thread+0xee>
    37c5:	4b 8d 14 f6          	lea    (%r14,%r14,8),%rdx
    37c9:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    37cd:	4d 8d 04 56          	lea    (%r14,%rdx,2),%r8
    37d1:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    37d5:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    37d9:	49 c1 e0 03          	shl    $0x3,%r8
    37dd:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    37e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    37e8:	89 f8                	mov    %edi,%eax
    37ea:	48 8b 71 20          	mov    0x20(%rcx),%rsi
    37ee:	99                   	cltd
    37ef:	f7 79 28             	idivl  0x28(%rcx)
    37f2:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    37f9:	48 63 d2             	movslq %edx,%rdx
    37fc:	48 8d 04 d2          	lea    (%rdx,%rdx,8),%rax
    3800:	48 8d 04 42          	lea    (%rdx,%rax,2),%rax
    3804:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
    3808:	4c 01 c6             	add    %r8,%rsi
    380b:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    3812:	c7 46 48 00 00 00 00 	movl   $0x0,0x48(%rsi)
    3819:	4c 39 c9             	cmp    %r9,%rcx
    381c:	75 ca                	jne    37e8 <timer_thread+0xb8>
    381e:	0f ae f0             	mfence
    3821:	49 8b 47 10          	mov    0x10(%r15),%rax
    3825:	39 78 28             	cmp    %edi,0x28(%rax)
    3828:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    382c:	0f 4e fb             	cmovle %ebx,%edi
    382f:	4c 63 f7             	movslq %edi,%r14
    3832:	85 c0                	test   %eax,%eax
    3834:	74 0d                	je     3843 <timer_thread+0x113>
    3836:	41 81 fd 30 75 00 00 	cmp    $0x7530,%r13d
    383d:	0f 85 67 ff ff ff    	jne    37aa <timer_thread+0x7a>
    3843:	48 8d 3d ee 27 00 00 	lea    0x27ee(%rip),%rdi        # 6038 <_IO_stdin_used+0x38>
    384a:	e8 81 ea ff ff       	call   22d0 <puts@plt>
    384f:	49 63 57 1c          	movslq 0x1c(%r15),%rdx
    3853:	85 d2                	test   %edx,%edx
    3855:	7e 5a                	jle    38b1 <timer_thread+0x181>
    3857:	49 63 47 28          	movslq 0x28(%r15),%rax
    385b:	85 c0                	test   %eax,%eax
    385d:	7e 52                	jle    38b1 <timer_thread+0x181>
    385f:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    3863:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3867:	48 8d 3c 4a          	lea    (%rdx,%rcx,2),%rdi
    386b:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    386f:	31 c9                	xor    %ecx,%ecx
    3871:	48 8d 34 50          	lea    (%rax,%rdx,2),%rsi
    3875:	48 c1 e7 03          	shl    $0x3,%rdi
    3879:	48 c1 e6 03          	shl    $0x3,%rsi
    387d:	49 8b 44 08 20       	mov    0x20(%r8,%rcx,1),%rax
    3882:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    3886:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    3890:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
    389a:	48 05 98 00 00 00    	add    $0x98,%rax
    38a0:	48 39 d0             	cmp    %rdx,%rax
    38a3:	75 eb                	jne    3890 <timer_thread+0x160>
    38a5:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    38ac:	48 39 f9             	cmp    %rdi,%rcx
    38af:	75 cc                	jne    387d <timer_thread+0x14d>
    38b1:	0f ae f0             	mfence
    38b4:	66 0f 6f 05 44 30 00 00 	movdqa 0x3044(%rip),%xmm0        # 6900 <_IO_stdin_used+0x900>
    38bc:	48 8d 2d 9a 27 00 00 	lea    0x279a(%rip),%rbp        # 605d <_IO_stdin_used+0x5d>
    38c3:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    38c8:	49 63 47 18          	movslq 0x18(%r15),%rax
    38cc:	45 8d 6e 01          	lea    0x1(%r14),%r13d
    38d0:	85 c0                	test   %eax,%eax
    38d2:	7e 53                	jle    3927 <timer_thread+0x1f7>
    38d4:	4b 8d 14 f6          	lea    (%r14,%r14,8),%rdx
    38d8:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    38dc:	49 8d 3c 56          	lea    (%r14,%rdx,2),%rdi
    38e0:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    38e4:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    38e8:	48 c1 e7 03          	shl    $0x3,%rdi
    38ec:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    38f0:	44 89 e8             	mov    %r13d,%eax
    38f3:	48 8b 71 20          	mov    0x20(%rcx),%rsi
    38f7:	99                   	cltd
    38f8:	f7 79 28             	idivl  0x28(%rcx)
    38fb:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3902:	48 63 c2             	movslq %edx,%rax
    3905:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3909:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    390d:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
    3911:	48 01 fe             	add    %rdi,%rsi
    3914:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    391b:	c7 46 48 00 00 00 00 	movl   $0x0,0x48(%rsi)
    3922:	49 39 c8             	cmp    %rcx,%r8
    3925:	75 c9                	jne    38f0 <timer_thread+0x1c0>
    3927:	0f ae f0             	mfence
    392a:	49 8b 47 10          	mov    0x10(%r15),%rax
    392e:	44 39 68 28          	cmp    %r13d,0x28(%rax)
    3932:	7f 03                	jg     3937 <timer_thread+0x207>
    3934:	45 31 ed             	xor    %r13d,%r13d
    3937:	45 8b 47 18          	mov    0x18(%r15),%r8d
    393b:	45 85 c0             	test   %r8d,%r8d
    393e:	0f 8e dd 00 00 00    	jle    3a21 <timer_thread+0x2f1>
    3944:	31 db                	xor    %ebx,%ebx
    3946:	45 31 e4             	xor    %r12d,%r12d
    3949:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    394f:	90                   	nop
    3950:	45 31 f6             	xor    %r14d,%r14d
    3953:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3958:	45 85 c0             	test   %r8d,%r8d
    395b:	0f 8e 81 00 00 00    	jle    39e2 <timer_thread+0x2b2>
    3961:	49 8b 47 10          	mov    0x10(%r15),%rax
    3965:	4b 8d 14 f6          	lea    (%r14,%r14,8),%rdx
    3969:	49 63 f8             	movslq %r8d,%rdi
    396c:	49 8d 14 56          	lea    (%r14,%rdx,2),%rdx
    3970:	48 8b 44 18 20       	mov    0x20(%rax,%rbx,1),%rax
    3975:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    3979:	31 d2                	xor    %edx,%edx
    397b:	eb 1e                	jmp    399b <timer_thread+0x26b>
    397d:	0f 1f 00             	nopl   (%rax)
    3980:	48 8b 71 70          	mov    0x70(%rcx),%rsi
    3984:	48 8b 74 06 08       	mov    0x8(%rsi,%rax,1),%rsi
    3989:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    398d:	48 85 f6             	test   %rsi,%rsi
    3990:	7f 21                	jg     39b3 <timer_thread+0x283>
    3992:	48 83 c2 01          	add    $0x1,%rdx
    3996:	48 39 d7             	cmp    %rdx,%rdi
    3999:	74 47                	je     39e2 <timer_thread+0x2b2>
    399b:	48 8b 71 70          	mov    0x70(%rcx),%rsi
    399f:	48 89 d0             	mov    %rdx,%rax
    39a2:	48 c1 e0 05          	shl    $0x5,%rax
    39a6:	48 8b 34 06          	mov    (%rsi,%rax,1),%rsi
    39aa:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    39ae:	48 85 f6             	test   %rsi,%rsi
    39b1:	7e cd                	jle    3980 <timer_thread+0x250>
    39b3:	48 8b 71 70          	mov    0x70(%rcx),%rsi
    39b7:	bf 01 00 00 00       	mov    $0x1,%edi
    39bc:	48 8b 74 06 08       	mov    0x8(%rsi,%rax,1),%rsi
    39c1:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    39c5:	48 8b 49 70          	mov    0x70(%rcx),%rcx
    39c9:	48 89 ee             	mov    %rbp,%rsi
    39cc:	48 8b 04 01          	mov    (%rcx,%rax,1),%rax
    39d0:	48 8b 48 08          	mov    0x8(%rax),%rcx
    39d4:	31 c0                	xor    %eax,%eax
    39d6:	e8 55 ea ff ff       	call   2430 <__printf_chk@plt>
    39db:	45 8b 47 18          	mov    0x18(%r15),%r8d
    39df:	45 31 c9             	xor    %r9d,%r9d
    39e2:	49 83 c6 01          	add    $0x1,%r14
    39e6:	45 39 f0             	cmp    %r14d,%r8d
    39e9:	0f 8f 69 ff ff ff    	jg     3958 <timer_thread+0x228>
    39ef:	41 83 c4 01          	add    $0x1,%r12d
    39f3:	45 39 c4             	cmp    %r8d,%r12d
    39f6:	7d 0c                	jge    3a04 <timer_thread+0x2d4>
    39f8:	48 81 c3 98 00 00 00 	add    $0x98,%rbx
    39ff:	e9 4c ff ff ff       	jmp    3950 <timer_thread+0x220>
    3a04:	41 83 f9 01          	cmp    $0x1,%r9d
    3a08:	74 17                	je     3a21 <timer_thread+0x2f1>
    3a0a:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    3a0f:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    3a14:	4d 63 f5             	movslq %r13d,%r14
    3a17:	e8 14 e9 ff ff       	call   2330 <nanosleep@plt>
    3a1c:	e9 a7 fe ff ff       	jmp    38c8 <timer_thread+0x198>
    3a21:	48 8d 3d 2c 26 00 00 	lea    0x262c(%rip),%rdi        # 6054 <_IO_stdin_used+0x54>
    3a28:	48 8d 2d 51 26 00 00 	lea    0x2651(%rip),%rbp        # 6080 <_IO_stdin_used+0x80>
    3a2f:	e8 9c e8 ff ff       	call   22d0 <puts@plt>
    3a34:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    3a38:	48 8d 1d 2f 26 00 00 	lea    0x262f(%rip),%rbx        # 606e <_IO_stdin_used+0x6e>
    3a3f:	85 c0                	test   %eax,%eax
    3a41:	0f 84 b6 00 00 00    	je     3afd <timer_thread+0x3cd>
    3a47:	41 8b 57 1c          	mov    0x1c(%r15),%edx
    3a4b:	45 31 e4             	xor    %r12d,%r12d
    3a4e:	45 31 ed             	xor    %r13d,%r13d
    3a51:	85 d2                	test   %edx,%edx
    3a53:	7e 29                	jle    3a7e <timer_thread+0x34e>
    3a55:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    3a59:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    3a5d:	83 78 04 02          	cmpl   $0x2,0x4(%rax)
    3a61:	c7 40 2c 00 00 00 00 	movl   $0x0,0x2c(%rax)
    3a68:	0f 84 bc 00 00 00    	je     3b2a <timer_thread+0x3fa>
    3a6e:	41 83 c5 01          	add    $0x1,%r13d
    3a72:	49 81 c4 98 00 00 00 	add    $0x98,%r12
    3a79:	41 39 d5             	cmp    %edx,%r13d
    3a7c:	7c db                	jl     3a59 <timer_thread+0x329>
    3a7e:	49 63 57 18          	movslq 0x18(%r15),%rdx
    3a82:	85 d2                	test   %edx,%edx
    3a84:	7e 58                	jle    3ade <timer_thread+0x3ae>
    3a86:	49 63 47 28          	movslq 0x28(%r15),%rax
    3a8a:	85 c0                	test   %eax,%eax
    3a8c:	7e 50                	jle    3ade <timer_thread+0x3ae>
    3a8e:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    3a92:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3a96:	48 8d 3c 4a          	lea    (%rdx,%rcx,2),%rdi
    3a9a:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3a9e:	31 c9                	xor    %ecx,%ecx
    3aa0:	48 8d 34 50          	lea    (%rax,%rdx,2),%rsi
    3aa4:	48 c1 e7 03          	shl    $0x3,%rdi
    3aa8:	48 c1 e6 03          	shl    $0x3,%rsi
    3aac:	0f 1f 40 00          	nopl   0x0(%rax)
    3ab0:	49 8b 44 08 20       	mov    0x20(%r8,%rcx,1),%rax
    3ab5:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    3ab9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3ac0:	c7 40 48 00 00 00 00 	movl   $0x0,0x48(%rax)
    3ac7:	48 05 98 00 00 00    	add    $0x98,%rax
    3acd:	48 39 d0             	cmp    %rdx,%rax
    3ad0:	75 ee                	jne    3ac0 <timer_thread+0x390>
    3ad2:	48 81 c1 98 00 00 00 	add    $0x98,%rcx
    3ad9:	48 39 f9             	cmp    %rdi,%rcx
    3adc:	75 d2                	jne    3ab0 <timer_thread+0x380>
    3ade:	0f ae f0             	mfence
    3ae1:	48 89 ef             	mov    %rbp,%rdi
    3ae4:	e8 e7 e7 ff ff       	call   22d0 <puts@plt>
    3ae9:	41 c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%r15)
    3af1:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    3af5:	85 c0                	test   %eax,%eax
    3af7:	0f 85 4a ff ff ff    	jne    3a47 <timer_thread+0x317>
    3afd:	48 8d 3d 83 25 00 00 	lea    0x2583(%rip),%rdi        # 6087 <_IO_stdin_used+0x87>
    3b04:	e8 c7 e7 ff ff       	call   22d0 <puts@plt>
    3b09:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3b0e:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3b17:	75 49                	jne    3b62 <timer_thread+0x432>
    3b19:	48 83 c4 58          	add    $0x58,%rsp
    3b1d:	31 c0                	xor    %eax,%eax
    3b1f:	5b                   	pop    %rbx
    3b20:	5d                   	pop    %rbp
    3b21:	41 5c                	pop    %r12
    3b23:	41 5d                	pop    %r13
    3b25:	41 5e                	pop    %r14
    3b27:	41 5f                	pop    %r15
    3b29:	c3                   	ret
    3b2a:	48 89 df             	mov    %rbx,%rdi
    3b2d:	41 83 c5 01          	add    $0x1,%r13d
    3b31:	e8 9a e7 ff ff       	call   22d0 <puts@plt>
    3b36:	49 8b 47 10          	mov    0x10(%r15),%rax
    3b3a:	be 01 00 00 00       	mov    $0x1,%esi
    3b3f:	42 8b 7c 20 48       	mov    0x48(%rax,%r12,1),%edi
    3b44:	49 81 c4 98 00 00 00 	add    $0x98,%r12
    3b4b:	e8 90 e8 ff ff       	call   23e0 <eventfd_write@plt>
    3b50:	41 8b 57 1c          	mov    0x1c(%r15),%edx
    3b54:	41 39 d5             	cmp    %edx,%r13d
    3b57:	0f 8c f8 fe ff ff    	jl     3a55 <timer_thread+0x325>
    3b5d:	e9 1c ff ff ff       	jmp    3a7e <timer_thread+0x34e>
    3b62:	e8 a9 e7 ff ff       	call   2310 <__stack_chk_fail@plt>
    3b67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000003b70 <fatal_error>:
    3b70:	f3 0f 1e fa          	endbr64
    3b74:	50                   	push   %rax
    3b75:	58                   	pop    %rax
    3b76:	48 83 ec 08          	sub    $0x8,%rsp
    3b7a:	e8 f1 e8 ff ff       	call   2470 <perror@plt>
    3b7f:	bf 01 00 00 00       	mov    $0x1,%edi
    3b84:	e8 f7 e8 ff ff       	call   2480 <exit@plt>
    3b89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003b90 <strtolower>:
    3b90:	f3 0f 1e fa          	endbr64
    3b94:	55                   	push   %rbp
    3b95:	53                   	push   %rbx
    3b96:	48 83 ec 08          	sub    $0x8,%rsp
    3b9a:	48 0f be 1f          	movsbq (%rdi),%rbx
    3b9e:	84 db                	test   %bl,%bl
    3ba0:	74 24                	je     3bc6 <strtolower+0x36>
    3ba2:	48 89 fd             	mov    %rdi,%rbp
    3ba5:	e8 46 e9 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3baa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3bb0:	48 8b 10             	mov    (%rax),%rdx
    3bb3:	48 83 c5 01          	add    $0x1,%rbp
    3bb7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    3bba:	88 55 ff             	mov    %dl,-0x1(%rbp)
    3bbd:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3bc2:	84 db                	test   %bl,%bl
    3bc4:	75 ea                	jne    3bb0 <strtolower+0x20>
    3bc6:	48 83 c4 08          	add    $0x8,%rsp
    3bca:	5b                   	pop    %rbx
    3bcb:	5d                   	pop    %rbp
    3bcc:	c3                   	ret
    3bcd:	0f 1f 00             	nopl   (%rax)

0000000000003bd0 <zh_malloc>:
    3bd0:	f3 0f 1e fa          	endbr64
    3bd4:	48 83 ec 08          	sub    $0x8,%rsp
    3bd8:	e8 13 e8 ff ff       	call   23f0 <malloc@plt>
    3bdd:	48 85 c0             	test   %rax,%rax
    3be0:	74 05                	je     3be7 <zh_malloc+0x17>
    3be2:	48 83 c4 08          	add    $0x8,%rsp
    3be6:	c3                   	ret
    3be7:	48 8b 0d 32 54 00 00 	mov    0x5432(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    3bee:	ba 28 00 00 00       	mov    $0x28,%edx
    3bf3:	be 01 00 00 00       	mov    $0x1,%esi
    3bf8:	48 8d 3d 21 28 00 00 	lea    0x2821(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    3bff:	e8 9c e8 ff ff       	call   24a0 <fwrite@plt>
    3c04:	bf 01 00 00 00       	mov    $0x1,%edi
    3c09:	e8 72 e8 ff ff       	call   2480 <exit@plt>
    3c0e:	66 90                	xchg   %ax,%ax

0000000000003c10 <get_filename_ext>:
    3c10:	f3 0f 1e fa          	endbr64
    3c14:	53                   	push   %rbx
    3c15:	be 2e 00 00 00       	mov    $0x2e,%esi
    3c1a:	48 89 fb             	mov    %rdi,%rbx
    3c1d:	e8 1e e7 ff ff       	call   2340 <strrchr@plt>
    3c22:	48 85 c0             	test   %rax,%rax
    3c25:	74 11                	je     3c38 <get_filename_ext+0x28>
    3c27:	48 39 c3             	cmp    %rax,%rbx
    3c2a:	74 0c                	je     3c38 <get_filename_ext+0x28>
    3c2c:	48 83 c0 01          	add    $0x1,%rax
    3c30:	5b                   	pop    %rbx
    3c31:	c3                   	ret
    3c32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3c38:	48 8d 05 90 24 00 00 	lea    0x2490(%rip),%rax        # 60cf <_IO_stdin_used+0xcf>
    3c3f:	5b                   	pop    %rbx
    3c40:	c3                   	ret
    3c41:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3c4c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003c50 <send_headers>:
    3c50:	f3 0f 1e fa          	endbr64
    3c54:	41 55                	push   %r13
    3c56:	49 89 f5             	mov    %rsi,%r13
    3c59:	48 89 fe             	mov    %rdi,%rsi
    3c5c:	41 54                	push   %r12
    3c5e:	55                   	push   %rbp
    3c5f:	48 89 d5             	mov    %rdx,%rbp
    3c62:	ba 00 04 00 00       	mov    $0x400,%edx
    3c67:	53                   	push   %rbx
    3c68:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    3c6f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3c78:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3c80:	31 c0                	xor    %eax,%eax
    3c82:	49 89 e4             	mov    %rsp,%r12
    3c85:	4c 89 e7             	mov    %r12,%rdi
    3c88:	e8 83 e7 ff ff       	call   2410 <__strcpy_chk@plt>
    3c8d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3c92:	84 db                	test   %bl,%bl
    3c94:	74 24                	je     3cba <send_headers+0x6a>
    3c96:	e8 55 e8 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    3c9b:	48 8b 08             	mov    (%rax),%rcx
    3c9e:	4c 89 e0             	mov    %r12,%rax
    3ca1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3ca8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    3cab:	48 83 c0 01          	add    $0x1,%rax
    3caf:	88 50 ff             	mov    %dl,-0x1(%rax)
    3cb2:	48 0f be 18          	movsbq (%rax),%rbx
    3cb6:	84 db                	test   %bl,%bl
    3cb8:	75 ee                	jne    3ca8 <send_headers+0x58>
    3cba:	bf 11 00 00 00       	mov    $0x11,%edi
    3cbf:	e8 2c e7 ff ff       	call   23f0 <malloc@plt>
    3cc4:	48 85 c0             	test   %rax,%rax
    3cc7:	0f 84 7e 04 00 00    	je     414b <send_headers+0x4fb>
    3ccd:	66 0f 6f 05 3b 2c 00 00 	movdqa 0x2c3b(%rip),%xmm0        # 6910 <_IO_stdin_used+0x910>
    3cd5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    3cd9:	bf 17 00 00 00       	mov    $0x17,%edi
    3cde:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3ce6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    3cea:	0f 11 00             	movups %xmm0,(%rax)
    3ced:	e8 fe e6 ff ff       	call   23f0 <malloc@plt>
    3cf2:	48 85 c0             	test   %rax,%rax
    3cf5:	0f 84 50 04 00 00    	je     414b <send_headers+0x4fb>
    3cfb:	66 0f 6f 05 1d 2c 00 00 	movdqa 0x2c1d(%rip),%xmm0        # 6920 <_IO_stdin_used+0x920>
    3d03:	48 89 45 10          	mov    %rax,0x10(%rbp)
    3d07:	4c 89 e7             	mov    %r12,%rdi
    3d0a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    3d14:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    3d1c:	0f 11 00             	movups %xmm0,(%rax)
    3d1f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    3d23:	be 2e 00 00 00       	mov    $0x2e,%esi
    3d28:	e8 13 e6 ff ff       	call   2340 <strrchr@plt>
    3d2d:	48 85 c0             	test   %rax,%rax
    3d30:	0f 84 ea 02 00 00    	je     4020 <send_headers+0x3d0>
    3d36:	4c 39 e0             	cmp    %r12,%rax
    3d39:	0f 84 e1 02 00 00    	je     4020 <send_headers+0x3d0>
    3d3f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    3d43:	48 8d 3d 53 23 00 00 	lea    0x2353(%rip),%rdi        # 609d <_IO_stdin_used+0x9d>
    3d4a:	48 89 de             	mov    %rbx,%rsi
    3d4d:	e8 3e e6 ff ff       	call   2390 <strcmp@plt>
    3d52:	85 c0                	test   %eax,%eax
    3d54:	75 20                	jne    3d76 <send_headers+0x126>
    3d56:	66 0f 6f 05 d2 2b 00 00 	movdqa 0x2bd2(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3d5e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3d66:	66 0f 6f 05 d2 2b 00 00 	movdqa 0x2bd2(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3d6e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    3d76:	48 89 de             	mov    %rbx,%rsi
    3d79:	48 8d 3d 21 23 00 00 	lea    0x2321(%rip),%rdi        # 60a1 <_IO_stdin_used+0xa1>
    3d80:	e8 0b e6 ff ff       	call   2390 <strcmp@plt>
    3d85:	85 c0                	test   %eax,%eax
    3d87:	75 20                	jne    3da9 <send_headers+0x159>
    3d89:	66 0f 6f 05 9f 2b 00 00 	movdqa 0x2b9f(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3d91:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3d99:	66 0f 6f 05 9f 2b 00 00 	movdqa 0x2b9f(%rip),%xmm0        # 6940 <_IO_stdin_used+0x940>
    3da1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    3da9:	48 89 de             	mov    %rbx,%rsi
    3dac:	48 8d 3d f3 22 00 00 	lea    0x22f3(%rip),%rdi        # 60a6 <_IO_stdin_used+0xa6>
    3db3:	e8 d8 e5 ff ff       	call   2390 <strcmp@plt>
    3db8:	85 c0                	test   %eax,%eax
    3dba:	0f 84 10 02 00 00    	je     3fd0 <send_headers+0x380>
    3dc0:	48 89 de             	mov    %rbx,%rsi
    3dc3:	48 8d 3d e0 22 00 00 	lea    0x22e0(%rip),%rdi        # 60aa <_IO_stdin_used+0xaa>
    3dca:	e8 c1 e5 ff ff       	call   2390 <strcmp@plt>
    3dcf:	85 c0                	test   %eax,%eax
    3dd1:	0f 84 a9 02 00 00    	je     4080 <send_headers+0x430>
    3dd7:	48 89 de             	mov    %rbx,%rsi
    3dda:	48 8d 3d cd 22 00 00 	lea    0x22cd(%rip),%rdi        # 60ae <_IO_stdin_used+0xae>
    3de1:	e8 aa e5 ff ff       	call   2390 <strcmp@plt>
    3de6:	85 c0                	test   %eax,%eax
    3de8:	0f 84 6a 02 00 00    	je     4058 <send_headers+0x408>
    3dee:	48 89 de             	mov    %rbx,%rsi
    3df1:	48 8d 3d f9 22 00 00 	lea    0x22f9(%rip),%rdi        # 60f1 <_IO_stdin_used+0xf1>
    3df8:	e8 93 e5 ff ff       	call   2390 <strcmp@plt>
    3dfd:	85 c0                	test   %eax,%eax
    3dff:	0f 84 2b 02 00 00    	je     4030 <send_headers+0x3e0>
    3e05:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3e08:	0f 84 52 01 00 00    	je     3f60 <send_headers+0x310>
    3e0e:	48 89 de             	mov    %rbx,%rsi
    3e11:	48 8d 3d 9a 22 00 00 	lea    0x229a(%rip),%rdi        # 60b2 <_IO_stdin_used+0xb2>
    3e18:	e8 73 e5 ff ff       	call   2390 <strcmp@plt>
    3e1d:	85 c0                	test   %eax,%eax
    3e1f:	0f 84 ab 02 00 00    	je     40d0 <send_headers+0x480>
    3e25:	48 89 de             	mov    %rbx,%rsi
    3e28:	48 8d 3d 87 22 00 00 	lea    0x2287(%rip),%rdi        # 60b6 <_IO_stdin_used+0xb6>
    3e2f:	e8 5c e5 ff ff       	call   2390 <strcmp@plt>
    3e34:	85 c0                	test   %eax,%eax
    3e36:	0f 84 6c 02 00 00    	je     40a8 <send_headers+0x458>
    3e3c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    3e44:	4c 89 e7             	mov    %r12,%rdi
    3e47:	e8 b4 e4 ff ff       	call   2300 <strlen@plt>
    3e4c:	48 89 c7             	mov    %rax,%rdi
    3e4f:	48 89 c3             	mov    %rax,%rbx
    3e52:	e8 99 e5 ff ff       	call   23f0 <malloc@plt>
    3e57:	48 85 c0             	test   %rax,%rax
    3e5a:	0f 84 eb 02 00 00    	je     414b <send_headers+0x4fb>
    3e60:	48 89 45 20          	mov    %rax,0x20(%rbp)
    3e64:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
    3e68:	83 fb 08             	cmp    $0x8,%ebx
    3e6b:	0f 83 3f 01 00 00    	jae    3fb0 <send_headers+0x360>
    3e71:	f6 c3 04             	test   $0x4,%bl
    3e74:	0f 85 7b 02 00 00    	jne    40f5 <send_headers+0x4a5>
    3e7a:	85 db                	test   %ebx,%ebx
    3e7c:	74 13                	je     3e91 <send_headers+0x241>
    3e7e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3e86:	88 10                	mov    %dl,(%rax)
    3e88:	f6 c3 02             	test   $0x2,%bl
    3e8b:	0f 85 96 02 00 00    	jne    4127 <send_headers+0x4d7>
    3e91:	4d 89 e8             	mov    %r13,%r8
    3e94:	48 8d 0d 1f 22 00 00 	lea    0x221f(%rip),%rcx        # 60ba <_IO_stdin_used+0xba>
    3e9b:	4c 89 e7             	mov    %r12,%rdi
    3e9e:	31 c0                	xor    %eax,%eax
    3ea0:	ba 00 04 00 00       	mov    $0x400,%edx
    3ea5:	be 01 00 00 00       	mov    $0x1,%esi
    3eaa:	e8 51 e6 ff ff       	call   2500 <__sprintf_chk@plt>
    3eaf:	4c 89 e7             	mov    %r12,%rdi
    3eb2:	e8 49 e4 ff ff       	call   2300 <strlen@plt>
    3eb7:	48 89 c7             	mov    %rax,%rdi
    3eba:	48 89 c3             	mov    %rax,%rbx
    3ebd:	e8 2e e5 ff ff       	call   23f0 <malloc@plt>
    3ec2:	48 85 c0             	test   %rax,%rax
    3ec5:	0f 84 80 02 00 00    	je     414b <send_headers+0x4fb>
    3ecb:	48 89 45 30          	mov    %rax,0x30(%rbp)
    3ecf:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    3ed3:	83 fb 08             	cmp    $0x8,%ebx
    3ed6:	0f 83 1c 01 00 00    	jae    3ff8 <send_headers+0x3a8>
    3edc:	f6 c3 04             	test   $0x4,%bl
    3edf:	0f 85 29 02 00 00    	jne    410e <send_headers+0x4be>
    3ee5:	85 db                	test   %ebx,%ebx
    3ee7:	74 13                	je     3efc <send_headers+0x2ac>
    3ee9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3ef1:	88 10                	mov    %dl,(%rax)
    3ef3:	f6 c3 02             	test   $0x2,%bl
    3ef6:	0f 85 3d 02 00 00    	jne    4139 <send_headers+0x4e9>
    3efc:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    3f01:	bf 02 00 00 00       	mov    $0x2,%edi
    3f06:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    3f0e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    3f16:	e8 d5 e4 ff ff       	call   23f0 <malloc@plt>
    3f1b:	48 85 c0             	test   %rax,%rax
    3f1e:	0f 84 27 02 00 00    	je     414b <send_headers+0x4fb>
    3f24:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    3f2c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    3f30:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    3f38:	66 89 10             	mov    %dx,(%rax)
    3f3b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    3f43:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3f4c:	0f 85 20 02 00 00    	jne    4172 <send_headers+0x522>
    3f52:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    3f59:	5b                   	pop    %rbx
    3f5a:	5d                   	pop    %rbp
    3f5b:	41 5c                	pop    %r12
    3f5d:	41 5d                	pop    %r13
    3f5f:	c3                   	ret
    3f60:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    3f64:	0f 85 a4 fe ff ff    	jne    3e0e <send_headers+0x1be>
    3f6a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    3f6e:	0f 85 9a fe ff ff    	jne    3e0e <send_headers+0x1be>
    3f74:	66 0f 6f 05 14 2a 00 00 	movdqa 0x2a14(%rip),%xmm0        # 6990 <_IO_stdin_used+0x990>
    3f7c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    3f86:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3f8e:	66 0f 6f 05 0a 2a 00 00 	movdqa 0x2a0a(%rip),%xmm0        # 69a0 <_IO_stdin_used+0x9a0>
    3f96:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    3f9e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    3fa6:	e9 63 fe ff ff       	jmp    3e0e <send_headers+0x1be>
    3fab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3fb0:	89 da                	mov    %ebx,%edx
    3fb2:	48 89 c7             	mov    %rax,%rdi
    3fb5:	4c 89 e6             	mov    %r12,%rsi
    3fb8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    3fbd:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    3fc2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    3fc5:	c1 e9 03             	shr    $0x3,%ecx
    3fc8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    3fcb:	e9 c1 fe ff ff       	jmp    3e91 <send_headers+0x241>
    3fd0:	66 0f 6f 05 58 29 00 00 	movdqa 0x2958(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    3fd8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3fe0:	66 0f 6f 05 68 29 00 00 	movdqa 0x2968(%rip),%xmm0        # 6950 <_IO_stdin_used+0x950>
    3fe8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    3ff0:	e9 cb fd ff ff       	jmp    3dc0 <send_headers+0x170>
    3ff5:	0f 1f 00             	nopl   (%rax)
    3ff8:	89 da                	mov    %ebx,%edx
    3ffa:	48 89 c7             	mov    %rax,%rdi
    3ffd:	4c 89 e6             	mov    %r12,%rsi
    4000:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4005:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    400a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    400d:	c1 e9 03             	shr    $0x3,%ecx
    4010:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4013:	e9 e4 fe ff ff       	jmp    3efc <send_headers+0x2ac>
    4018:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4020:	48 8d 1d a8 20 00 00 	lea    0x20a8(%rip),%rbx        # 60cf <_IO_stdin_used+0xcf>
    4027:	e9 94 fd ff ff       	jmp    3dc0 <send_headers+0x170>
    402c:	0f 1f 40 00          	nopl   0x0(%rax)
    4030:	66 0f 6f 05 38 29 00 00 	movdqa 0x2938(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4038:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4040:	66 0f 6f 05 38 29 00 00 	movdqa 0x2938(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    4048:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4050:	e9 b0 fd ff ff       	jmp    3e05 <send_headers+0x1b5>
    4055:	0f 1f 00             	nopl   (%rax)
    4058:	66 0f 6f 05 10 29 00 00 	movdqa 0x2910(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    4060:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4068:	66 0f 6f 05 10 29 00 00 	movdqa 0x2910(%rip),%xmm0        # 6980 <_IO_stdin_used+0x980>
    4070:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4078:	e9 71 fd ff ff       	jmp    3dee <send_headers+0x19e>
    407d:	0f 1f 00             	nopl   (%rax)
    4080:	66 0f 6f 05 a8 28 00 00 	movdqa 0x28a8(%rip),%xmm0        # 6930 <_IO_stdin_used+0x930>
    4088:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4090:	66 0f 6f 05 c8 28 00 00 	movdqa 0x28c8(%rip),%xmm0        # 6960 <_IO_stdin_used+0x960>
    4098:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    40a0:	e9 32 fd ff ff       	jmp    3dd7 <send_headers+0x187>
    40a5:	0f 1f 00             	nopl   (%rax)
    40a8:	66 0f 6f 05 c0 28 00 00 	movdqa 0x28c0(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    40b0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40b8:	66 0f 6f 05 00 29 00 00 	movdqa 0x2900(%rip),%xmm0        # 69c0 <_IO_stdin_used+0x9c0>
    40c0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    40c8:	e9 6f fd ff ff       	jmp    3e3c <send_headers+0x1ec>
    40cd:	0f 1f 00             	nopl   (%rax)
    40d0:	66 0f 6f 05 98 28 00 00 	movdqa 0x2898(%rip),%xmm0        # 6970 <_IO_stdin_used+0x970>
    40d8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    40e0:	66 0f 6f 05 c8 28 00 00 	movdqa 0x28c8(%rip),%xmm0        # 69b0 <_IO_stdin_used+0x9b0>
    40e8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    40f0:	e9 30 fd ff ff       	jmp    3e25 <send_headers+0x1d5>
    40f5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    40fc:	89 db                	mov    %ebx,%ebx
    40fe:	89 10                	mov    %edx,(%rax)
    4100:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4105:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4109:	e9 83 fd ff ff       	jmp    3e91 <send_headers+0x241>
    410e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4115:	89 db                	mov    %ebx,%ebx
    4117:	89 10                	mov    %edx,(%rax)
    4119:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    411e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4122:	e9 d5 fd ff ff       	jmp    3efc <send_headers+0x2ac>
    4127:	89 db                	mov    %ebx,%ebx
    4129:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    412f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4134:	e9 58 fd ff ff       	jmp    3e91 <send_headers+0x241>
    4139:	89 db                	mov    %ebx,%ebx
    413b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4141:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4146:	e9 b1 fd ff ff       	jmp    3efc <send_headers+0x2ac>
    414b:	48 8b 0d ce 4e 00 00 	mov    0x4ece(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4152:	ba 28 00 00 00       	mov    $0x28,%edx
    4157:	be 01 00 00 00       	mov    $0x1,%esi
    415c:	48 8d 3d bd 22 00 00 	lea    0x22bd(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    4163:	e8 38 e3 ff ff       	call   24a0 <fwrite@plt>
    4168:	bf 01 00 00 00       	mov    $0x1,%edi
    416d:	e8 0e e3 ff ff       	call   2480 <exit@plt>
    4172:	e8 99 e1 ff ff       	call   2310 <__stack_chk_fail@plt>
    4177:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004180 <copy_file_contents>:
    4180:	f3 0f 1e fa          	endbr64
    4184:	41 55                	push   %r13
    4186:	49 89 d5             	mov    %rdx,%r13
    4189:	41 54                	push   %r12
    418b:	49 89 fc             	mov    %rdi,%r12
    418e:	48 89 f7             	mov    %rsi,%rdi
    4191:	55                   	push   %rbp
    4192:	53                   	push   %rbx
    4193:	48 89 f3             	mov    %rsi,%rbx
    4196:	48 83 ec 08          	sub    $0x8,%rsp
    419a:	e8 51 e2 ff ff       	call   23f0 <malloc@plt>
    419f:	48 85 c0             	test   %rax,%rax
    41a2:	74 77                	je     421b <copy_file_contents+0x9b>
    41a4:	4c 89 e7             	mov    %r12,%rdi
    41a7:	48 89 c5             	mov    %rax,%rbp
    41aa:	31 f6                	xor    %esi,%esi
    41ac:	31 c0                	xor    %eax,%eax
    41ae:	e8 ad e2 ff ff       	call   2460 <open@plt>
    41b3:	41 89 c4             	mov    %eax,%r12d
    41b6:	85 c0                	test   %eax,%eax
    41b8:	78 55                	js     420f <copy_file_contents+0x8f>
    41ba:	48 89 da             	mov    %rbx,%rdx
    41bd:	48 89 ee             	mov    %rbp,%rsi
    41c0:	89 c7                	mov    %eax,%edi
    41c2:	e8 a9 e1 ff ff       	call   2370 <read@plt>
    41c7:	48 98                	cltq
    41c9:	48 39 d8             	cmp    %rbx,%rax
    41cc:	7c 22                	jl     41f0 <copy_file_contents+0x70>
    41ce:	44 89 e7             	mov    %r12d,%edi
    41d1:	e8 7a e1 ff ff       	call   2350 <close@plt>
    41d6:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    41da:	49 89 5d 08          	mov    %rbx,0x8(%r13)
    41de:	48 83 c4 08          	add    $0x8,%rsp
    41e2:	5b                   	pop    %rbx
    41e3:	5d                   	pop    %rbp
    41e4:	41 5c                	pop    %r12
    41e6:	41 5d                	pop    %r13
    41e8:	c3                   	ret
    41e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    41f0:	48 8b 0d 29 4e 00 00 	mov    0x4e29(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    41f7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    41fc:	be 01 00 00 00       	mov    $0x1,%esi
    4201:	48 8d 3d c8 1e 00 00 	lea    0x1ec8(%rip),%rdi        # 60d0 <_IO_stdin_used+0xd0>
    4208:	e8 93 e2 ff ff       	call   24a0 <fwrite@plt>
    420d:	eb bf                	jmp    41ce <copy_file_contents+0x4e>
    420f:	48 8d 3d e9 1f 00 00 	lea    0x1fe9(%rip),%rdi        # 61ff <_IO_stdin_used+0x1ff>
    4216:	e8 55 f9 ff ff       	call   3b70 <fatal_error>
    421b:	48 8b 0d fe 4d 00 00 	mov    0x4dfe(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4222:	ba 28 00 00 00       	mov    $0x28,%edx
    4227:	be 01 00 00 00       	mov    $0x1,%esi
    422c:	48 8d 3d ed 21 00 00 	lea    0x21ed(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    4233:	e8 68 e2 ff ff       	call   24a0 <fwrite@plt>
    4238:	bf 01 00 00 00       	mov    $0x1,%edi
    423d:	e8 3e e2 ff ff       	call   2480 <exit@plt>
    4242:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    424d:	0f 1f 00             	nopl   (%rax)

0000000000004250 <add_write_request>:
    4250:	f3 0f 1e fa          	endbr64
    4254:	8b 46 44             	mov    0x44(%rsi),%eax
    4257:	48 89 fa             	mov    %rdi,%rdx
    425a:	48 89 f7             	mov    %rsi,%rdi
    425d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    4263:	8d 70 01             	lea    0x1(%rax),%esi
    4266:	48 8b 07             	mov    (%rdi),%rax
    4269:	44 8b 00             	mov    (%rax),%r8d
    426c:	f6 c1 02             	test   $0x2,%cl
    426f:	74 00                	je     4271 <add_write_request+0x21>
    4271:	89 f0                	mov    %esi,%eax
    4273:	44 29 c0             	sub    %r8d,%eax
    4276:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    4279:	0f 82 a1 e2 ff ff    	jb     2520 <add_write_request.cold>
    427f:	c1 e9 0a             	shr    $0xa,%ecx
    4282:	48 83 ec 08          	sub    $0x8,%rsp
    4286:	8b 47 44             	mov    0x44(%rdi),%eax
    4289:	23 47 58             	and    0x58(%rdi),%eax
    428c:	83 e1 01             	and    $0x1,%ecx
    428f:	89 77 44             	mov    %esi,0x44(%rdi)
    4292:	8b 72 08             	mov    0x8(%rdx),%esi
    4295:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4299:	d3 e0                	shl    %cl,%eax
    429b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    429e:	48 c1 e0 06          	shl    $0x6,%rax
    42a2:	48 03 47 38          	add    0x38(%rdi),%rax
    42a6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    42ac:	89 70 04             	mov    %esi,0x4(%rax)
    42af:	48 8d 72 10          	lea    0x10(%rdx),%rsi
    42b3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    42b9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    42c1:	48 89 70 10          	mov    %rsi,0x10(%rax)
    42c5:	89 48 18             	mov    %ecx,0x18(%rax)
    42c8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    42cf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    42d7:	48 89 50 20          	mov    %rdx,0x20(%rax)
    42db:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    42df:	e8 3c e0 ff ff       	call   2320 <io_uring_submit@plt>
    42e4:	31 c0                	xor    %eax,%eax
    42e6:	48 83 c4 08          	add    $0x8,%rsp
    42ea:	c3                   	ret
    42eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000042f0 <add_read_request>:
    42f0:	f3 0f 1e fa          	endbr64
    42f4:	41 55                	push   %r13
    42f6:	41 89 fd             	mov    %edi,%r13d
    42f9:	41 54                	push   %r12
    42fb:	55                   	push   %rbp
    42fc:	53                   	push   %rbx
    42fd:	48 89 f3             	mov    %rsi,%rbx
    4300:	48 83 ec 08          	sub    $0x8,%rsp
    4304:	8b 46 44             	mov    0x44(%rsi),%eax
    4307:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
    430d:	48 8b 16             	mov    (%rsi),%rdx
    4310:	83 c0 01             	add    $0x1,%eax
    4313:	8b 32                	mov    (%rdx),%esi
    4315:	f6 c1 02             	test   $0x2,%cl
    4318:	74 00                	je     431a <add_read_request+0x2a>
    431a:	89 c2                	mov    %eax,%edx
    431c:	29 f2                	sub    %esi,%edx
    431e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    4321:	0f 82 09 e2 ff ff    	jb     2530 <add_read_request.cold>
    4327:	8b 6b 44             	mov    0x44(%rbx),%ebp
    432a:	c1 e9 0a             	shr    $0xa,%ecx
    432d:	89 43 44             	mov    %eax,0x44(%rbx)
    4330:	bf 20 00 00 00       	mov    $0x20,%edi
    4335:	83 e1 01             	and    $0x1,%ecx
    4338:	23 6b 58             	and    0x58(%rbx),%ebp
    433b:	d3 e5                	shl    %cl,%ebp
    433d:	48 c1 e5 06          	shl    $0x6,%rbp
    4341:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4345:	e8 a6 e0 ff ff       	call   23f0 <malloc@plt>
    434a:	be 01 00 00 00       	mov    $0x1,%esi
    434f:	bf 00 20 00 00       	mov    $0x2000,%edi
    4354:	49 89 c4             	mov    %rax,%r12
    4357:	e8 24 e0 ff ff       	call   2380 <calloc@plt>
    435c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    4361:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4365:	48 89 df             	mov    %rbx,%rdi
    4368:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    436d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    4372:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    437b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    4383:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
    4387:	4c 89 65 20          	mov    %r12,0x20(%rbp)
    438b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
    4392:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    439a:	48 89 45 10          	mov    %rax,0x10(%rbp)
    439e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
    43a6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    43ae:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    43b2:	e8 69 df ff ff       	call   2320 <io_uring_submit@plt>
    43b7:	48 83 c4 08          	add    $0x8,%rsp
    43bb:	31 c0                	xor    %eax,%eax
    43bd:	5b                   	pop    %rbx
    43be:	5d                   	pop    %rbp
    43bf:	41 5c                	pop    %r12
    43c1:	41 5d                	pop    %r13
    43c3:	c3                   	ret
    43c4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    43cf:	90                   	nop

00000000000043d0 <_send_static_string_content>:
    43d0:	f3 0f 1e fa          	endbr64
    43d4:	41 56                	push   %r14
    43d6:	41 89 f6             	mov    %esi,%r14d
    43d9:	41 55                	push   %r13
    43db:	49 89 fd             	mov    %rdi,%r13
    43de:	bf 20 00 00 00       	mov    $0x20,%edi
    43e3:	41 54                	push   %r12
    43e5:	55                   	push   %rbp
    43e6:	48 89 d5             	mov    %rdx,%rbp
    43e9:	53                   	push   %rbx
    43ea:	e8 01 e0 ff ff       	call   23f0 <malloc@plt>
    43ef:	48 85 c0             	test   %rax,%rax
    43f2:	0f 84 dd 00 00 00    	je     44d5 <_send_static_string_content+0x105>
    43f8:	48 89 c3             	mov    %rax,%rbx
    43fb:	4c 89 ef             	mov    %r13,%rdi
    43fe:	e8 fd de ff ff       	call   2300 <strlen@plt>
    4403:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    440a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    440e:	48 89 c7             	mov    %rax,%rdi
    4411:	49 89 c4             	mov    %rax,%r12
    4414:	e8 d7 df ff ff       	call   23f0 <malloc@plt>
    4419:	48 89 c7             	mov    %rax,%rdi
    441c:	48 85 c0             	test   %rax,%rax
    441f:	0f 84 b0 00 00 00    	je     44d5 <_send_static_string_content+0x105>
    4425:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4429:	4c 89 e2             	mov    %r12,%rdx
    442c:	4c 89 ee             	mov    %r13,%rsi
    442f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    4433:	e8 88 df ff ff       	call   23c0 <memcpy@plt>
    4438:	8b 45 44             	mov    0x44(%rbp),%eax
    443b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
    4441:	8d 50 01             	lea    0x1(%rax),%edx
    4444:	48 8b 45 00          	mov    0x0(%rbp),%rax
    4448:	8b 30                	mov    (%rax),%esi
    444a:	f6 c1 02             	test   $0x2,%cl
    444d:	0f 85 7d 00 00 00    	jne    44d0 <_send_static_string_content+0x100>
    4453:	89 d0                	mov    %edx,%eax
    4455:	29 f0                	sub    %esi,%eax
    4457:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    445a:	0f 82 da e0 ff ff    	jb     253a <_send_static_string_content.cold>
    4460:	c1 e9 0a             	shr    $0xa,%ecx
    4463:	8b 45 44             	mov    0x44(%rbp),%eax
    4466:	23 45 58             	and    0x58(%rbp),%eax
    4469:	89 55 44             	mov    %edx,0x44(%rbp)
    446c:	83 e1 01             	and    $0x1,%ecx
    446f:	8b 53 04             	mov    0x4(%rbx),%edx
    4472:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    4478:	66 0f ef c0          	pxor   %xmm0,%xmm0
    447c:	d3 e0                	shl    %cl,%eax
    447e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    4481:	48 89 ef             	mov    %rbp,%rdi
    4484:	48 c1 e0 06          	shl    $0x6,%rax
    4488:	48 03 45 38          	add    0x38(%rbp),%rax
    448c:	89 48 04             	mov    %ecx,0x4(%rax)
    448f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
    4493:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    4499:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    44a1:	48 89 48 10          	mov    %rcx,0x10(%rax)
    44a5:	89 50 18             	mov    %edx,0x18(%rax)
    44a8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    44af:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    44b7:	48 89 58 20          	mov    %rbx,0x20(%rax)
    44bb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    44bf:	5b                   	pop    %rbx
    44c0:	5d                   	pop    %rbp
    44c1:	41 5c                	pop    %r12
    44c3:	41 5d                	pop    %r13
    44c5:	41 5e                	pop    %r14
    44c7:	e9 54 de ff ff       	jmp    2320 <io_uring_submit@plt>
    44cc:	0f 1f 40 00          	nopl   0x0(%rax)
    44d0:	e9 7e ff ff ff       	jmp    4453 <_send_static_string_content+0x83>
    44d5:	48 8b 0d 44 4b 00 00 	mov    0x4b44(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    44dc:	ba 28 00 00 00       	mov    $0x28,%edx
    44e1:	be 01 00 00 00       	mov    $0x1,%esi
    44e6:	48 8d 3d 33 1f 00 00 	lea    0x1f33(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    44ed:	e8 ae df ff ff       	call   24a0 <fwrite@plt>
    44f2:	bf 01 00 00 00       	mov    $0x1,%edi
    44f7:	e8 84 df ff ff       	call   2480 <exit@plt>
    44fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004500 <handle_unimplemented_method>:
    4500:	f3 0f 1e fa          	endbr64
    4504:	48 89 f2             	mov    %rsi,%rdx
    4507:	89 fe                	mov    %edi,%esi
    4509:	48 8b 3d 08 4b 00 00 	mov    0x4b08(%rip),%rdi        # 9018 <unimplemented_content>
    4510:	e9 bb fe ff ff       	jmp    43d0 <_send_static_string_content>
    4515:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004520 <handle_http_404>:
    4520:	f3 0f 1e fa          	endbr64
    4524:	48 89 f2             	mov    %rsi,%rdx
    4527:	89 fe                	mov    %edi,%esi
    4529:	48 8b 3d e0 4a 00 00 	mov    0x4ae0(%rip),%rdi        # 9010 <http_404_content>
    4530:	e9 9b fe ff ff       	jmp    43d0 <_send_static_string_content>
    4535:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004540 <handle_get_method>:
    4540:	f3 0f 1e fa          	endbr64
    4544:	41 56                	push   %r14
    4546:	41 55                	push   %r13
    4548:	49 89 d5             	mov    %rdx,%r13
    454b:	41 54                	push   %r12
    454d:	41 89 f4             	mov    %esi,%r12d
    4550:	55                   	push   %rbp
    4551:	48 89 fd             	mov    %rdi,%rbp
    4554:	53                   	push   %rbx
    4555:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    455c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4565:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    456d:	31 c0                	xor    %eax,%eax
    456f:	e8 8c dd ff ff       	call   2300 <strlen@plt>
    4574:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4579:	48 89 c3             	mov    %rax,%rbx
    457c:	0f 84 b6 00 00 00    	je     4638 <handle_get_method+0xf8>
    4582:	b8 69 63 00 00       	mov    $0x6369,%eax
    4587:	48 89 ee             	mov    %rbp,%rsi
    458a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    458e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4593:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    459b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    45a3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    45ae:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
    45b6:	e8 e5 dd ff ff       	call   23a0 <__memcpy_chk@plt>
    45bb:	48 89 e6             	mov    %rsp,%rsi
    45be:	4c 89 f7             	mov    %r14,%rdi
    45c1:	e8 ea dd ff ff       	call   23b0 <stat@plt>
    45c6:	83 f8 ff             	cmp    $0xffffffff,%eax
    45c9:	0f 84 d3 00 00 00    	je     46a2 <handle_get_method+0x162>
    45cf:	8b 44 24 18          	mov    0x18(%rsp),%eax
    45d3:	25 00 f0 00 00       	and    $0xf000,%eax
    45d8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    45dd:	0f 84 f5 00 00 00    	je     46d8 <handle_get_method+0x198>
    45e3:	48 8b 3d 26 4a 00 00 	mov    0x4a26(%rip),%rdi        # 9010 <http_404_content>
    45ea:	4c 89 ea             	mov    %r13,%rdx
    45ed:	44 89 e6             	mov    %r12d,%esi
    45f0:	e8 db fd ff ff       	call   43d0 <_send_static_string_content>
    45f5:	4c 89 f2             	mov    %r14,%rdx
    45f8:	bf 01 00 00 00       	mov    $0x1,%edi
    45fd:	31 c0                	xor    %eax,%eax
    45ff:	48 8d 35 1a 1b 00 00 	lea    0x1b1a(%rip),%rsi        # 6120 <_IO_stdin_used+0x120>
    4606:	e8 25 de ff ff       	call   2430 <__printf_chk@plt>
    460b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    4613:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    461c:	0f 85 20 01 00 00    	jne    4742 <handle_get_method+0x202>
    4622:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    4629:	5b                   	pop    %rbx
    462a:	5d                   	pop    %rbp
    462b:	41 5c                	pop    %r12
    462d:	41 5d                	pop    %r13
    462f:	41 5e                	pop    %r14
    4631:	c3                   	ret
    4632:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4638:	ba 69 63 00 00       	mov    $0x6369,%edx
    463d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    4645:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    464a:	48 89 ee             	mov    %rbp,%rsi
    464d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
    4655:	48 89 c2             	mov    %rax,%rdx
    4658:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4660:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    466b:	e8 30 dd ff ff       	call   23a0 <__memcpy_chk@plt>
    4670:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4675:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    467a:	48 8d 35 6a 1a 00 00 	lea    0x1a6a(%rip),%rsi        # 60eb <_IO_stdin_used+0xeb>
    4681:	48 29 d9             	sub    %rbx,%rcx
    4684:	ba 0b 00 00 00       	mov    $0xb,%edx
    4689:	e8 12 dd ff ff       	call   23a0 <__memcpy_chk@plt>
    468e:	48 89 e6             	mov    %rsp,%rsi
    4691:	4c 89 f7             	mov    %r14,%rdi
    4694:	e8 17 dd ff ff       	call   23b0 <stat@plt>
    4699:	83 f8 ff             	cmp    $0xffffffff,%eax
    469c:	0f 85 2d ff ff ff    	jne    45cf <handle_get_method+0x8f>
    46a2:	4c 89 f2             	mov    %r14,%rdx
    46a5:	48 89 e9             	mov    %rbp,%rcx
    46a8:	48 8d 35 47 1a 00 00 	lea    0x1a47(%rip),%rsi        # 60f6 <_IO_stdin_used+0xf6>
    46af:	31 c0                	xor    %eax,%eax
    46b1:	bf 01 00 00 00       	mov    $0x1,%edi
    46b6:	e8 75 dd ff ff       	call   2430 <__printf_chk@plt>
    46bb:	48 8b 3d 4e 49 00 00 	mov    0x494e(%rip),%rdi        # 9010 <http_404_content>
    46c2:	4c 89 ea             	mov    %r13,%rdx
    46c5:	44 89 e6             	mov    %r12d,%esi
    46c8:	e8 03 fd ff ff       	call   43d0 <_send_static_string_content>
    46cd:	e9 39 ff ff ff       	jmp    460b <handle_get_method+0xcb>
    46d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    46d8:	bf 70 00 00 00       	mov    $0x70,%edi
    46dd:	e8 0e dd ff ff       	call   23f0 <malloc@plt>
    46e2:	48 89 c3             	mov    %rax,%rbx
    46e5:	48 85 c0             	test   %rax,%rax
    46e8:	74 5d                	je     4747 <handle_get_method+0x207>
    46ea:	44 89 60 08          	mov    %r12d,0x8(%rax)
    46ee:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    46f3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    46f7:	4c 89 f7             	mov    %r14,%rdi
    46fa:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
    4701:	e8 4a f5 ff ff       	call   3c50 <send_headers>
    4706:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    470b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    470f:	4c 89 f7             	mov    %r14,%rdi
    4712:	e8 69 fa ff ff       	call   4180 <copy_file_contents>
    4717:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    471c:	4c 89 f2             	mov    %r14,%rdx
    471f:	31 c0                	xor    %eax,%eax
    4721:	48 8d 35 e6 19 00 00 	lea    0x19e6(%rip),%rsi        # 610e <_IO_stdin_used+0x10e>
    4728:	bf 01 00 00 00       	mov    $0x1,%edi
    472d:	e8 fe dc ff ff       	call   2430 <__printf_chk@plt>
    4732:	4c 89 ee             	mov    %r13,%rsi
    4735:	48 89 df             	mov    %rbx,%rdi
    4738:	e8 13 fb ff ff       	call   4250 <add_write_request>
    473d:	e9 c9 fe ff ff       	jmp    460b <handle_get_method+0xcb>
    4742:	e8 c9 db ff ff       	call   2310 <__stack_chk_fail@plt>
    4747:	48 8b 0d d2 48 00 00 	mov    0x48d2(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    474e:	ba 28 00 00 00       	mov    $0x28,%edx
    4753:	be 01 00 00 00       	mov    $0x1,%esi
    4758:	48 8d 3d c1 1c 00 00 	lea    0x1cc1(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    475f:	e8 3c dd ff ff       	call   24a0 <fwrite@plt>
    4764:	bf 01 00 00 00       	mov    $0x1,%edi
    4769:	e8 12 dd ff ff       	call   2480 <exit@plt>
    476e:	66 90                	xchg   %ax,%ax

0000000000004770 <handle_http_method>:
    4770:	f3 0f 1e fa          	endbr64
    4774:	41 57                	push   %r15
    4776:	41 56                	push   %r14
    4778:	4c 8d 35 06 19 00 00 	lea    0x1906(%rip),%r14        # 6085 <_IO_stdin_used+0x85>
    477f:	41 55                	push   %r13
    4781:	49 89 d5             	mov    %rdx,%r13
    4784:	41 54                	push   %r12
    4786:	41 89 f4             	mov    %esi,%r12d
    4789:	4c 89 f6             	mov    %r14,%rsi
    478c:	55                   	push   %rbp
    478d:	53                   	push   %rbx
    478e:	48 83 ec 18          	sub    $0x18,%rsp
    4792:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    479b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    47a0:	31 c0                	xor    %eax,%eax
    47a2:	49 89 e7             	mov    %rsp,%r15
    47a5:	4c 89 fa             	mov    %r15,%rdx
    47a8:	e8 b3 db ff ff       	call   2360 <strtok_r@plt>
    47ad:	48 0f be 18          	movsbq (%rax),%rbx
    47b1:	48 89 c5             	mov    %rax,%rbp
    47b4:	84 db                	test   %bl,%bl
    47b6:	74 1d                	je     47d5 <handle_http_method+0x65>
    47b8:	e8 33 dd ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    47bd:	48 89 ea             	mov    %rbp,%rdx
    47c0:	48 8b 08             	mov    (%rax),%rcx
    47c3:	48 83 c2 01          	add    $0x1,%rdx
    47c7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    47ca:	88 4a ff             	mov    %cl,-0x1(%rdx)
    47cd:	48 0f be 1a          	movsbq (%rdx),%rbx
    47d1:	84 db                	test   %bl,%bl
    47d3:	75 eb                	jne    47c0 <handle_http_method+0x50>
    47d5:	4c 89 fa             	mov    %r15,%rdx
    47d8:	4c 89 f6             	mov    %r14,%rsi
    47db:	31 ff                	xor    %edi,%edi
    47dd:	e8 7e db ff ff       	call   2360 <strtok_r@plt>
    47e2:	48 8d 35 4a 19 00 00 	lea    0x194a(%rip),%rsi        # 6133 <_IO_stdin_used+0x133>
    47e9:	48 89 ef             	mov    %rbp,%rdi
    47ec:	48 89 c3             	mov    %rax,%rbx
    47ef:	e8 9c db ff ff       	call   2390 <strcmp@plt>
    47f4:	4c 89 ea             	mov    %r13,%rdx
    47f7:	44 89 e6             	mov    %r12d,%esi
    47fa:	85 c0                	test   %eax,%eax
    47fc:	75 2a                	jne    4828 <handle_http_method+0xb8>
    47fe:	48 89 df             	mov    %rbx,%rdi
    4801:	e8 3a fd ff ff       	call   4540 <handle_get_method>
    4806:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    480b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4814:	75 20                	jne    4836 <handle_http_method+0xc6>
    4816:	48 83 c4 18          	add    $0x18,%rsp
    481a:	5b                   	pop    %rbx
    481b:	5d                   	pop    %rbp
    481c:	41 5c                	pop    %r12
    481e:	41 5d                	pop    %r13
    4820:	41 5e                	pop    %r14
    4822:	41 5f                	pop    %r15
    4824:	c3                   	ret
    4825:	0f 1f 00             	nopl   (%rax)
    4828:	48 8b 3d e9 47 00 00 	mov    0x47e9(%rip),%rdi        # 9018 <unimplemented_content>
    482f:	e8 9c fb ff ff       	call   43d0 <_send_static_string_content>
    4834:	eb d0                	jmp    4806 <handle_http_method+0x96>
    4836:	e8 d5 da ff ff       	call   2310 <__stack_chk_fail@plt>
    483b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004840 <get_line>:
    4840:	f3 0f 1e fa          	endbr64
    4844:	85 d2                	test   %edx,%edx
    4846:	7e 38                	jle    4880 <get_line+0x40>
    4848:	48 63 d2             	movslq %edx,%rdx
    484b:	48 83 c7 01          	add    $0x1,%rdi
    484f:	48 01 f2             	add    %rsi,%rdx
    4852:	eb 11                	jmp    4865 <get_line+0x25>
    4854:	0f 1f 40 00          	nopl   0x0(%rax)
    4858:	48 83 c6 01          	add    $0x1,%rsi
    485c:	48 83 c7 01          	add    $0x1,%rdi
    4860:	48 39 d6             	cmp    %rdx,%rsi
    4863:	74 1b                	je     4880 <get_line+0x40>
    4865:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4869:	88 06                	mov    %al,(%rsi)
    486b:	3c 0d                	cmp    $0xd,%al
    486d:	75 e9                	jne    4858 <get_line+0x18>
    486f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4872:	75 e4                	jne    4858 <get_line+0x18>
    4874:	c6 06 00             	movb   $0x0,(%rsi)
    4877:	31 c0                	xor    %eax,%eax
    4879:	c3                   	ret
    487a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4880:	b8 01 00 00 00       	mov    $0x1,%eax
    4885:	c3                   	ret
    4886:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004890 <handle_client_request>:
    4890:	f3 0f 1e fa          	endbr64
    4894:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    489b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    489f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    48a8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    48b0:	31 c0                	xor    %eax,%eax
    48b2:	49 89 e2             	mov    %rsp,%r10
    48b5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    48bd:	4c 89 d0             	mov    %r10,%rax
    48c0:	eb 13                	jmp    48d5 <handle_client_request+0x45>
    48c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    48c8:	48 83 c0 01          	add    $0x1,%rax
    48cc:	48 83 c1 01          	add    $0x1,%rcx
    48d0:	4c 39 c8             	cmp    %r9,%rax
    48d3:	74 4b                	je     4920 <handle_client_request+0x90>
    48d5:	44 0f b6 01          	movzbl (%rcx),%r8d
    48d9:	44 88 00             	mov    %r8b,(%rax)
    48dc:	41 80 f8 0d          	cmp    $0xd,%r8b
    48e0:	75 e6                	jne    48c8 <handle_client_request+0x38>
    48e2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    48e6:	75 e0                	jne    48c8 <handle_client_request+0x38>
    48e8:	c6 00 00             	movb   $0x0,(%rax)
    48eb:	8b 47 08             	mov    0x8(%rdi),%eax
    48ee:	48 89 f2             	mov    %rsi,%rdx
    48f1:	4c 89 d7             	mov    %r10,%rdi
    48f4:	89 c6                	mov    %eax,%esi
    48f6:	e8 75 fe ff ff       	call   4770 <handle_http_method>
    48fb:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    4903:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    490c:	75 39                	jne    4947 <handle_client_request+0xb7>
    490e:	31 c0                	xor    %eax,%eax
    4910:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    4917:	c3                   	ret
    4918:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4920:	48 8b 0d f9 46 00 00 	mov    0x46f9(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4927:	ba 12 00 00 00       	mov    $0x12,%edx
    492c:	be 01 00 00 00       	mov    $0x1,%esi
    4931:	48 8d 3d ff 17 00 00 	lea    0x17ff(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    4938:	e8 63 db ff ff       	call   24a0 <fwrite@plt>
    493d:	bf 01 00 00 00       	mov    $0x1,%edi
    4942:	e8 39 db ff ff       	call   2480 <exit@plt>
    4947:	e8 c4 d9 ff ff       	call   2310 <__stack_chk_fail@plt>
    494c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004950 <add_accept_request>:
    4950:	f3 0f 1e fa          	endbr64
    4954:	55                   	push   %rbp
    4955:	53                   	push   %rbx
    4956:	48 89 cb             	mov    %rcx,%rbx
    4959:	48 83 ec 08          	sub    $0x8,%rsp
    495d:	8b 41 44             	mov    0x44(%rcx),%eax
    4960:	4c 8b 03             	mov    (%rbx),%r8
    4963:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
    4969:	83 c0 01             	add    $0x1,%eax
    496c:	45 8b 08             	mov    (%r8),%r9d
    496f:	f6 c1 02             	test   $0x2,%cl
    4972:	74 00                	je     4974 <add_accept_request+0x24>
    4974:	41 89 c0             	mov    %eax,%r8d
    4977:	45 29 c8             	sub    %r9d,%r8d
    497a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    497e:	0f 82 c6 db ff ff    	jb     254a <add_accept_request.cold>
    4984:	c1 e9 0a             	shr    $0xa,%ecx
    4987:	8b 6b 44             	mov    0x44(%rbx),%ebp
    498a:	23 6b 58             	and    0x58(%rbx),%ebp
    498d:	89 43 44             	mov    %eax,0x44(%rbx)
    4990:	83 e1 01             	and    $0x1,%ecx
    4993:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4997:	d3 e5                	shl    %cl,%ebp
    4999:	48 c1 e5 06          	shl    $0x6,%rbp
    499d:	48 03 6b 38          	add    0x38(%rbx),%rbp
    49a1:	89 7d 04             	mov    %edi,0x4(%rbp)
    49a4:	bf 10 00 00 00       	mov    $0x10,%edi
    49a9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
    49b0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    49b4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
    49b8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    49c0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
    49c8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    49cc:	e8 1f da ff ff       	call   23f0 <malloc@plt>
    49d1:	48 89 df             	mov    %rbx,%rdi
    49d4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    49da:	48 89 45 20          	mov    %rax,0x20(%rbp)
    49de:	48 83 c4 08          	add    $0x8,%rsp
    49e2:	5b                   	pop    %rbx
    49e3:	5d                   	pop    %rbp
    49e4:	e9 37 d9 ff ff       	jmp    2320 <io_uring_submit@plt>
    49e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000049f0 <io_thread>:
    49f0:	f3 0f 1e fa          	endbr64
    49f4:	41 57                	push   %r15
    49f6:	31 d2                	xor    %edx,%edx
    49f8:	41 56                	push   %r14
    49fa:	41 55                	push   %r13
    49fc:	41 54                	push   %r12
    49fe:	55                   	push   %rbp
    49ff:	48 89 fd             	mov    %rdi,%rbp
    4a02:	53                   	push   %rbx
    4a03:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    4a0a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4a13:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    4a1b:	48 8b 47 40          	mov    0x40(%rdi),%rax
    4a1f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    4a24:	bf 00 01 00 00       	mov    $0x100,%edi
    4a29:	48 89 de             	mov    %rbx,%rsi
    4a2c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    4a30:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    4a35:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    4a3a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    4a3f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    4a44:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    4a4c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    4a51:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    4a59:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    4a5e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4a66:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    4a6b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4a73:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4a78:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4a80:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4a85:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    4a8d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4a95:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    4a9d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4aa5:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    4aad:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4ab5:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    4abd:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4ac5:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    4acd:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4ad5:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    4add:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4ae4:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
    4aec:	e8 df d8 ff ff       	call   23d0 <io_uring_queue_init@plt>
    4af1:	48 8b 7d 40          	mov    0x40(%rbp),%rdi
    4af5:	31 f6                	xor    %esi,%esi
    4af7:	e8 c4 d9 ff ff       	call   24c0 <io_uring_register_eventfd@plt>
    4afc:	31 d2                	xor    %edx,%edx
    4afe:	be 01 00 00 00       	mov    $0x1,%esi
    4b03:	bf 02 00 00 00       	mov    $0x2,%edi
    4b08:	e8 03 da ff ff       	call   2510 <socket@plt>
    4b0d:	83 f8 ff             	cmp    $0xffffffff,%eax
    4b10:	0f 84 08 06 00 00    	je     511e <io_thread+0x72e>
    4b16:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    4b1b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    4b21:	89 c7                	mov    %eax,%edi
    4b23:	41 89 c4             	mov    %eax,%r12d
    4b26:	ba 02 00 00 00       	mov    $0x2,%edx
    4b2b:	be 01 00 00 00       	mov    $0x1,%esi
    4b30:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    4b38:	e8 a3 d7 ff ff       	call   22e0 <setsockopt@plt>
    4b3d:	85 c0                	test   %eax,%eax
    4b3f:	0f 88 cd 05 00 00    	js     5112 <io_thread+0x722>
    4b45:	8b 05 95 1e 00 00    	mov    0x1e95(%rip),%eax        # 69e0 <_IO_stdin_used+0x9e0>
    4b4b:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    4b50:	ba 10 00 00 00       	mov    $0x10,%edx
    4b55:	44 89 e7             	mov    %r12d,%edi
    4b58:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4b61:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    4b69:	89 44 24 40          	mov    %eax,0x40(%rsp)
    4b6d:	e8 ce d8 ff ff       	call   2440 <bind@plt>
    4b72:	85 c0                	test   %eax,%eax
    4b74:	0f 88 8c 05 00 00    	js     5106 <io_thread+0x716>
    4b7a:	be 0a 00 00 00       	mov    $0xa,%esi
    4b7f:	44 89 e7             	mov    %r12d,%edi
    4b82:	e8 79 d8 ff ff       	call   2400 <listen@plt>
    4b87:	85 c0                	test   %eax,%eax
    4b89:	0f 88 6b 05 00 00    	js     50fa <io_thread+0x70a>
    4b8f:	ba 50 00 00 00       	mov    $0x50,%edx
    4b94:	48 8d 35 e1 15 00 00 	lea    0x15e1(%rip),%rsi        # 617c <_IO_stdin_used+0x17c>
    4b9b:	bf 01 00 00 00       	mov    $0x1,%edi
    4ba0:	31 c0                	xor    %eax,%eax
    4ba2:	e8 89 d8 ff ff       	call   2430 <__printf_chk@plt>
    4ba7:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    4bac:	48 89 d9             	mov    %rbx,%rcx
    4baf:	44 89 e7             	mov    %r12d,%edi
    4bb2:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4bb7:	48 89 c6             	mov    %rax,%rsi
    4bba:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    4bbf:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
    4bc4:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
    4bcc:	e8 7f fd ff ff       	call   4950 <add_accept_request>
    4bd1:	bf 01 00 00 00       	mov    $0x1,%edi
    4bd6:	be 10 00 00 00       	mov    $0x10,%esi
    4bdb:	e8 a0 d7 ff ff       	call   2380 <calloc@plt>
    4be0:	bf 0a 00 00 00       	mov    $0xa,%edi
    4be5:	49 89 c5             	mov    %rax,%r13
    4be8:	e8 03 d8 ff ff       	call   23f0 <malloc@plt>
    4bed:	48 85 c0             	test   %rax,%rax
    4bf0:	0f 84 dd 04 00 00    	je     50d3 <io_thread+0x6e3>
    4bf6:	49 89 45 00          	mov    %rax,0x0(%r13)
    4bfa:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4c01:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4c08:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
    4c10:	8d 50 01             	lea    0x1(%rax),%edx
    4c13:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4c18:	8b 30                	mov    (%rax),%esi
    4c1a:	f6 c1 02             	test   $0x2,%cl
    4c1d:	0f 85 2d 04 00 00    	jne    5050 <io_thread+0x660>
    4c23:	89 d0                	mov    %edx,%eax
    4c25:	29 f0                	sub    %esi,%eax
    4c27:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4c2e:	0f 82 20 d9 ff ff    	jb     2554 <io_thread.cold>
    4c34:	c1 e9 0a             	shr    $0xa,%ecx
    4c37:	48 8d 75 48          	lea    0x48(%rbp),%rsi
    4c3b:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4c3f:	48 89 df             	mov    %rbx,%rdi
    4c42:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4c49:	83 e1 01             	and    $0x1,%ecx
    4c4c:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    4c53:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    4c5a:	d3 e0                	shl    %cl,%eax
    4c5c:	8b 55 48             	mov    0x48(%rbp),%edx
    4c5f:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4c64:	48 c1 e0 06          	shl    $0x6,%rax
    4c68:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    4c70:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    4c76:	89 50 04             	mov    %edx,0x4(%rax)
    4c79:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4c81:	4c 89 68 10          	mov    %r13,0x10(%rax)
    4c85:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    4c8d:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4c95:	48 89 70 20          	mov    %rsi,0x20(%rax)
    4c99:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    4c9d:	e8 7e d6 ff ff       	call   2320 <io_uring_submit@plt>
    4ca2:	8b 45 2c             	mov    0x2c(%rbp),%eax
    4ca5:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    4caa:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4cb2:	83 f8 01             	cmp    $0x1,%eax
    4cb5:	0f 85 b8 01 00 00    	jne    4e73 <io_thread+0x483>
    4cbb:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4cc0:	4d 89 ce             	mov    %r9,%r14
    4cc3:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4cc8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4cd0:	48 8d 3d bb 14 00 00 	lea    0x14bb(%rip),%rdi        # 6192 <_IO_stdin_used+0x192>
    4cd7:	e8 f4 d5 ff ff       	call   22d0 <puts@plt>
    4cdc:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4ce3:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
    4cea:	c1 e9 0b             	shr    $0xb,%ecx
    4ced:	83 e1 01             	and    $0x1,%ecx
    4cf0:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4cf8:	8b 00                	mov    (%rax),%eax
    4cfa:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    4d02:	8b 16                	mov    (%rsi),%edx
    4d04:	39 d0                	cmp    %edx,%eax
    4d06:	74 36                	je     4d3e <io_thread+0x34e>
    4d08:	89 f8                	mov    %edi,%eax
    4d0a:	21 d0                	and    %edx,%eax
    4d0c:	d3 e0                	shl    %cl,%eax
    4d0e:	48 c1 e0 04          	shl    $0x4,%rax
    4d12:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
    4d1a:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    4d22:	0f 85 88 01 00 00    	jne    4eb0 <io_thread+0x4c0>
    4d28:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    4d2c:	0f 85 26 03 00 00    	jne    5058 <io_thread+0x668>
    4d32:	8b 40 08             	mov    0x8(%rax),%eax
    4d35:	83 c2 01             	add    $0x1,%edx
    4d38:	89 16                	mov    %edx,(%rsi)
    4d3a:	85 c0                	test   %eax,%eax
    4d3c:	79 b2                	jns    4cf0 <io_thread+0x300>
    4d3e:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    4d47:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4d50:	45 31 c0             	xor    %r8d,%r8d
    4d53:	31 d2                	xor    %edx,%edx
    4d55:	b9 01 00 00 00       	mov    $0x1,%ecx
    4d5a:	4c 89 f6             	mov    %r14,%rsi
    4d5d:	48 89 df             	mov    %rbx,%rdi
    4d60:	e8 bb d6 ff ff       	call   2420 <__io_uring_get_cqe@plt>
    4d65:	41 89 c7             	mov    %eax,%r15d
    4d68:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4d6d:	48 83 38 01          	cmpq   $0x1,(%rax)
    4d71:	0f 84 f1 02 00 00    	je     5068 <io_thread+0x678>
    4d77:	48 8d 3d 3a 14 00 00 	lea    0x143a(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4d7e:	e8 4d d5 ff ff       	call   22d0 <puts@plt>
    4d83:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4d88:	4c 8b 22             	mov    (%rdx),%r12
    4d8b:	45 85 ff             	test   %r15d,%r15d
    4d8e:	0f 88 2e 03 00 00    	js     50c2 <io_thread+0x6d2>
    4d94:	8b 42 08             	mov    0x8(%rdx),%eax
    4d97:	45 8b 04 24          	mov    (%r12),%r8d
    4d9b:	85 c0                	test   %eax,%eax
    4d9d:	0f 88 e5 02 00 00    	js     5088 <io_thread+0x698>
    4da3:	41 83 f8 01          	cmp    $0x1,%r8d
    4da7:	0f 84 3b 01 00 00    	je     4ee8 <io_thread+0x4f8>
    4dad:	41 83 f8 02          	cmp    $0x2,%r8d
    4db1:	0f 84 b1 01 00 00    	je     4f68 <io_thread+0x578>
    4db7:	45 85 c0             	test   %r8d,%r8d
    4dba:	0f 84 70 01 00 00    	je     4f30 <io_thread+0x540>
    4dc0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    4dc8:	8b 02                	mov    (%rdx),%eax
    4dca:	83 c0 01             	add    $0x1,%eax
    4dcd:	89 02                	mov    %eax,(%rdx)
    4dcf:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4dd6:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4ddd:	8d 50 01             	lea    0x1(%rax),%edx
    4de0:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4de5:	8b 30                	mov    (%rax),%esi
    4de7:	f6 c1 02             	test   $0x2,%cl
    4dea:	74 00                	je     4dec <io_thread+0x3fc>
    4dec:	89 d0                	mov    %edx,%eax
    4dee:	29 f0                	sub    %esi,%eax
    4df0:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4df7:	0f 82 57 d7 ff ff    	jb     2554 <io_thread.cold>
    4dfd:	c1 e9 0a             	shr    $0xa,%ecx
    4e00:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    4e05:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4e09:	48 89 df             	mov    %rbx,%rdi
    4e0c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4e13:	83 e1 01             	and    $0x1,%ecx
    4e16:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    4e1d:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    4e24:	d3 e0                	shl    %cl,%eax
    4e26:	8b 55 48             	mov    0x48(%rbp),%edx
    4e29:	48 c1 e0 06          	shl    $0x6,%rax
    4e2d:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    4e35:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    4e3b:	89 50 04             	mov    %edx,0x4(%rax)
    4e3e:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4e46:	4c 89 68 10          	mov    %r13,0x10(%rax)
    4e4a:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    4e52:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4e5a:	48 89 70 20          	mov    %rsi,0x20(%rax)
    4e5e:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    4e62:	e8 b9 d4 ff ff       	call   2320 <io_uring_submit@plt>
    4e67:	8b 45 2c             	mov    0x2c(%rbp),%eax
    4e6a:	83 f8 01             	cmp    $0x1,%eax
    4e6d:	0f 84 5d fe ff ff    	je     4cd0 <io_thread+0x2e0>
    4e73:	48 8d 3d 77 13 00 00 	lea    0x1377(%rip),%rdi        # 61f1 <_IO_stdin_used+0x1f1>
    4e7a:	e8 51 d4 ff ff       	call   22d0 <puts@plt>
    4e7f:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    4e87:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4e90:	0f 85 38 02 00 00    	jne    50ce <io_thread+0x6de>
    4e96:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    4e9d:	31 c0                	xor    %eax,%eax
    4e9f:	5b                   	pop    %rbx
    4ea0:	5d                   	pop    %rbp
    4ea1:	41 5c                	pop    %r12
    4ea3:	41 5d                	pop    %r13
    4ea5:	41 5e                	pop    %r14
    4ea7:	41 5f                	pop    %r15
    4ea9:	c3                   	ret
    4eaa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4eb0:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    4eb5:	48 85 c0             	test   %rax,%rax
    4eb8:	0f 84 92 fe ff ff    	je     4d50 <io_thread+0x360>
    4ebe:	48 83 38 01          	cmpq   $0x1,(%rax)
    4ec2:	0f 84 a0 01 00 00    	je     5068 <io_thread+0x678>
    4ec8:	48 8d 3d e9 12 00 00 	lea    0x12e9(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4ecf:	e8 fc d3 ff ff       	call   22d0 <puts@plt>
    4ed4:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4ed9:	4c 8b 22             	mov    (%rdx),%r12
    4edc:	e9 b3 fe ff ff       	jmp    4d94 <io_thread+0x3a4>
    4ee1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4ee8:	85 c0                	test   %eax,%eax
    4eea:	0f 85 c0 00 00 00    	jne    4fb0 <io_thread+0x5c0>
    4ef0:	48 8b 0d 29 41 00 00 	mov    0x4129(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4ef7:	ba 0f 00 00 00       	mov    $0xf,%edx
    4efc:	be 01 00 00 00       	mov    $0x1,%esi
    4f01:	48 8d 3d d9 12 00 00 	lea    0x12d9(%rip),%rdi        # 61e1 <_IO_stdin_used+0x1e1>
    4f08:	e8 93 d5 ff ff       	call   24a0 <fwrite@plt>
    4f0d:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4f12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4f18:	48 85 c0             	test   %rax,%rax
    4f1b:	0f 84 ae fe ff ff    	je     4dcf <io_thread+0x3df>
    4f21:	e9 9a fe ff ff       	jmp    4dc0 <io_thread+0x3d0>
    4f26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4f30:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    4f35:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    4f3a:	48 89 d9             	mov    %rbx,%rcx
    4f3d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    4f41:	e8 0a fa ff ff       	call   4950 <add_accept_request>
    4f46:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4f4b:	48 89 de             	mov    %rbx,%rsi
    4f4e:	8b 78 08             	mov    0x8(%rax),%edi
    4f51:	e8 9a f3 ff ff       	call   42f0 <add_read_request>
    4f56:	4c 89 e7             	mov    %r12,%rdi
    4f59:	e8 52 d3 ff ff       	call   22b0 <free@plt>
    4f5e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4f63:	eb b3                	jmp    4f18 <io_thread+0x528>
    4f65:	0f 1f 00             	nopl   (%rax)
    4f68:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    4f6d:	45 31 ff             	xor    %r15d,%r15d
    4f70:	85 c0                	test   %eax,%eax
    4f72:	7e 20                	jle    4f94 <io_thread+0x5a4>
    4f74:	0f 1f 40 00          	nopl   0x0(%rax)
    4f78:	4c 89 f8             	mov    %r15,%rax
    4f7b:	49 83 c7 01          	add    $0x1,%r15
    4f7f:	48 c1 e0 04          	shl    $0x4,%rax
    4f83:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    4f88:	e8 23 d3 ff ff       	call   22b0 <free@plt>
    4f8d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    4f92:	7f e4                	jg     4f78 <io_thread+0x588>
    4f94:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    4f99:	e8 b2 d3 ff ff       	call   2350 <close@plt>
    4f9e:	4c 89 e7             	mov    %r12,%rdi
    4fa1:	e8 0a d3 ff ff       	call   22b0 <free@plt>
    4fa6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4fab:	e9 68 ff ff ff       	jmp    4f18 <io_thread+0x528>
    4fb0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    4fb5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4fba:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    4fc2:	eb 11                	jmp    4fd5 <io_thread+0x5e5>
    4fc4:	0f 1f 40 00          	nopl   0x0(%rax)
    4fc8:	48 83 c0 01          	add    $0x1,%rax
    4fcc:	48 83 c2 01          	add    $0x1,%rdx
    4fd0:	48 39 c6             	cmp    %rax,%rsi
    4fd3:	74 4b                	je     5020 <io_thread+0x630>
    4fd5:	0f b6 0a             	movzbl (%rdx),%ecx
    4fd8:	88 08                	mov    %cl,(%rax)
    4fda:	80 f9 0d             	cmp    $0xd,%cl
    4fdd:	75 e9                	jne    4fc8 <io_thread+0x5d8>
    4fdf:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    4fe3:	75 e3                	jne    4fc8 <io_thread+0x5d8>
    4fe5:	c6 00 00             	movb   $0x0,(%rax)
    4fe8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    4fed:	48 89 da             	mov    %rbx,%rdx
    4ff0:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    4ff5:	e8 76 f7 ff ff       	call   4770 <handle_http_method>
    4ffa:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    4fff:	e8 ac d2 ff ff       	call   22b0 <free@plt>
    5004:	4c 89 e7             	mov    %r12,%rdi
    5007:	e8 a4 d2 ff ff       	call   22b0 <free@plt>
    500c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5011:	e9 02 ff ff ff       	jmp    4f18 <io_thread+0x528>
    5016:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5020:	48 8b 0d f9 3f 00 00 	mov    0x3ff9(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    5027:	ba 12 00 00 00       	mov    $0x12,%edx
    502c:	be 01 00 00 00       	mov    $0x1,%esi
    5031:	48 8d 3d ff 10 00 00 	lea    0x10ff(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    5038:	e8 63 d4 ff ff       	call   24a0 <fwrite@plt>
    503d:	bf 01 00 00 00       	mov    $0x1,%edi
    5042:	e8 39 d4 ff ff       	call   2480 <exit@plt>
    5047:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    5050:	e9 ce fb ff ff       	jmp    4c23 <io_thread+0x233>
    5055:	0f 1f 00             	nopl   (%rax)
    5058:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    505d:	e9 5c fe ff ff       	jmp    4ebe <io_thread+0x4ce>
    5062:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5068:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5070:	48 8d 3d 2d 11 00 00 	lea    0x112d(%rip),%rdi        # 61a4 <_IO_stdin_used+0x1a4>
    5077:	8b 02                	mov    (%rdx),%eax
    5079:	83 c0 01             	add    $0x1,%eax
    507c:	89 02                	mov    %eax,(%rdx)
    507e:	e8 4d d2 ff ff       	call   22d0 <puts@plt>
    5083:	e9 eb fd ff ff       	jmp    4e73 <io_thread+0x483>
    5088:	f7 d8                	neg    %eax
    508a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    508f:	89 c7                	mov    %eax,%edi
    5091:	e8 4a d4 ff ff       	call   24e0 <strerror@plt>
    5096:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    509b:	be 01 00 00 00       	mov    $0x1,%esi
    50a0:	48 8b 3d 79 3f 00 00 	mov    0x3f79(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    50a7:	48 89 c1             	mov    %rax,%rcx
    50aa:	48 8d 15 9f 13 00 00 	lea    0x139f(%rip),%rdx        # 6450 <_IO_stdin_used+0x450>
    50b1:	31 c0                	xor    %eax,%eax
    50b3:	e8 f8 d3 ff ff       	call   24b0 <__fprintf_chk@plt>
    50b8:	bf 01 00 00 00       	mov    $0x1,%edi
    50bd:	e8 be d3 ff ff       	call   2480 <exit@plt>
    50c2:	48 8d 3d 06 11 00 00 	lea    0x1106(%rip),%rdi        # 61cf <_IO_stdin_used+0x1cf>
    50c9:	e8 a2 ea ff ff       	call   3b70 <fatal_error>
    50ce:	e8 3d d2 ff ff       	call   2310 <__stack_chk_fail@plt>
    50d3:	48 8b 0d 46 3f 00 00 	mov    0x3f46(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    50da:	ba 28 00 00 00       	mov    $0x28,%edx
    50df:	be 01 00 00 00       	mov    $0x1,%esi
    50e4:	48 8d 3d 35 13 00 00 	lea    0x1335(%rip),%rdi        # 6420 <_IO_stdin_used+0x420>
    50eb:	e8 b0 d3 ff ff       	call   24a0 <fwrite@plt>
    50f0:	bf 01 00 00 00       	mov    $0x1,%edi
    50f5:	e8 86 d3 ff ff       	call   2480 <exit@plt>
    50fa:	48 8d 3d 72 10 00 00 	lea    0x1072(%rip),%rdi        # 6173 <_IO_stdin_used+0x173>
    5101:	e8 6a ea ff ff       	call   3b70 <fatal_error>
    5106:	48 8d 3d 5f 10 00 00 	lea    0x105f(%rip),%rdi        # 616c <_IO_stdin_used+0x16c>
    510d:	e8 5e ea ff ff       	call   3b70 <fatal_error>
    5112:	48 8d 3d 3a 10 00 00 	lea    0x103a(%rip),%rdi        # 6153 <_IO_stdin_used+0x153>
    5119:	e8 52 ea ff ff       	call   3b70 <fatal_error>
    511e:	48 8d 3d 25 10 00 00 	lea    0x1025(%rip),%rdi        # 614a <_IO_stdin_used+0x14a>
    5125:	e8 46 ea ff ff       	call   3b70 <fatal_error>
    512a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005130 <receive>:
    5130:	f3 0f 1e fa          	endbr64
    5134:	8b 57 3c             	mov    0x3c(%rdi),%edx
    5137:	85 d2                	test   %edx,%edx
    5139:	0f 8e d1 00 00 00    	jle    5210 <receive+0xe0>
    513f:	48 89 f8             	mov    %rdi,%rax
    5142:	45 31 db             	xor    %r11d,%r11d
    5145:	0f 1f 00             	nopl   (%rax)
    5148:	48 8b 50 70          	mov    0x70(%rax),%rdx
    514c:	4c 89 df             	mov    %r11,%rdi
    514f:	48 c1 e7 05          	shl    $0x5,%rdi
    5153:	4c 8b 0c 3a          	mov    (%rdx,%rdi,1),%r9
    5157:	49 8b 51 08          	mov    0x8(%r9),%rdx
    515b:	48 85 d2             	test   %rdx,%rdx
    515e:	0f 8e 94 00 00 00    	jle    51f8 <receive+0xc8>
    5164:	4d 8b 11             	mov    (%r9),%r10
    5167:	31 d2                	xor    %edx,%edx
    5169:	eb 12                	jmp    517d <receive+0x4d>
    516b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5170:	49 8b 49 08          	mov    0x8(%r9),%rcx
    5174:	48 83 c2 01          	add    $0x1,%rdx
    5178:	48 39 d1             	cmp    %rdx,%rcx
    517b:	7e 7b                	jle    51f8 <receive+0xc8>
    517d:	48 8b 48 78          	mov    0x78(%rax),%rcx
    5181:	49 8b 34 d2          	mov    (%r10,%rdx,8),%rsi
    5185:	48 83 c1 01          	add    $0x1,%rcx
    5189:	4c 8b 46 10          	mov    0x10(%rsi),%r8
    518d:	48 89 48 78          	mov    %rcx,0x78(%rax)
    5191:	48 8b 48 10          	mov    0x10(%rax),%rcx
    5195:	48 83 c1 01          	add    $0x1,%rcx
    5199:	48 89 48 10          	mov    %rcx,0x10(%rax)
    519d:	48 8b 48 70          	mov    0x70(%rax),%rcx
    51a1:	48 83 44 39 18 01    	addq   $0x1,0x18(%rcx,%rdi,1)
    51a7:	48 63 08             	movslq (%rax),%rcx
    51aa:	49 39 c8             	cmp    %rcx,%r8
    51ad:	75 c1                	jne    5170 <receive+0x40>
    51af:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    51b3:	48 63 48 38          	movslq 0x38(%rax),%rcx
    51b7:	48 39 ce             	cmp    %rcx,%rsi
    51ba:	75 b4                	jne    5170 <receive+0x40>
    51bc:	48 83 ec 08          	sub    $0x8,%rsp
    51c0:	48 63 50 38          	movslq 0x38(%rax),%rdx
    51c4:	48 63 00             	movslq (%rax),%rax
    51c7:	31 c9                	xor    %ecx,%ecx
    51c9:	bf 01 00 00 00       	mov    $0x1,%edi
    51ce:	48 39 f2             	cmp    %rsi,%rdx
    51d1:	48 8d 35 a0 12 00 00 	lea    0x12a0(%rip),%rsi        # 6478 <_IO_stdin_used+0x478>
    51d8:	0f 94 c1             	sete   %cl
    51db:	31 d2                	xor    %edx,%edx
    51dd:	4c 39 c0             	cmp    %r8,%rax
    51e0:	0f 94 c2             	sete   %dl
    51e3:	31 c0                	xor    %eax,%eax
    51e5:	e8 46 d2 ff ff       	call   2430 <__printf_chk@plt>
    51ea:	bf 01 00 00 00       	mov    $0x1,%edi
    51ef:	e8 8c d2 ff ff       	call   2480 <exit@plt>
    51f4:	0f 1f 40 00          	nopl   0x0(%rax)
    51f8:	49 c7 41 08 00 00 00 00 	movq   $0x0,0x8(%r9)
    5200:	8b 50 3c             	mov    0x3c(%rax),%edx
    5203:	49 83 c3 01          	add    $0x1,%r11
    5207:	44 39 da             	cmp    %r11d,%edx
    520a:	0f 8f 38 ff ff ff    	jg     5148 <receive+0x18>
    5210:	c3                   	ret
    5211:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    521c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005220 <barriered_work>:
    5220:	f3 0f 1e fa          	endbr64
    5224:	41 55                	push   %r13
    5226:	41 54                	push   %r12
    5228:	55                   	push   %rbp
    5229:	53                   	push   %rbx
    522a:	48 89 fb             	mov    %rdi,%rbx
    522d:	48 83 ec 08          	sub    $0x8,%rsp
    5231:	8b 57 38             	mov    0x38(%rdi),%edx
    5234:	8b 07                	mov    (%rdi),%eax
    5236:	39 c2                	cmp    %eax,%edx
    5238:	0f 84 d2 00 00 00    	je     5310 <barriered_work+0xf0>
    523e:	e8 ed fe ff ff       	call   5130 <receive>
    5243:	8b 43 48             	mov    0x48(%rbx),%eax
    5246:	83 f8 01             	cmp    $0x1,%eax
    5249:	75 19                	jne    5264 <barriered_work+0x44>
    524b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5250:	48 8b 43 10          	mov    0x10(%rbx),%rax
    5254:	48 83 c0 01          	add    $0x1,%rax
    5258:	48 89 43 10          	mov    %rax,0x10(%rbx)
    525c:	8b 43 48             	mov    0x48(%rbx),%eax
    525f:	83 f8 01             	cmp    $0x1,%eax
    5262:	74 ec                	je     5250 <barriered_work+0x30>
    5264:	8b 83 80 00 00 00    	mov    0x80(%rbx),%eax
    526a:	83 f8 01             	cmp    $0x1,%eax
    526d:	74 10                	je     527f <barriered_work+0x5f>
    526f:	0f ae f0             	mfence
    5272:	48 83 c4 08          	add    $0x8,%rsp
    5276:	31 c0                	xor    %eax,%eax
    5278:	5b                   	pop    %rbx
    5279:	5d                   	pop    %rbp
    527a:	41 5c                	pop    %r12
    527c:	41 5d                	pop    %r13
    527e:	c3                   	ret
    527f:	8b 43 3c             	mov    0x3c(%rbx),%eax
    5282:	85 c0                	test   %eax,%eax
    5284:	7e e9                	jle    526f <barriered_work+0x4f>
    5286:	45 31 c9             	xor    %r9d,%r9d
    5289:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5290:	8b 43 38             	mov    0x38(%rbx),%eax
    5293:	44 39 c8             	cmp    %r9d,%eax
    5296:	74 5e                	je     52f6 <barriered_work+0xd6>
    5298:	48 8b 43 70          	mov    0x70(%rbx),%rax
    529c:	4c 89 c9             	mov    %r9,%rcx
    529f:	48 c1 e1 05          	shl    $0x5,%rcx
    52a3:	48 8b 54 08 08       	mov    0x8(%rax,%rcx,1),%rdx
    52a8:	48 8b 42 08          	mov    0x8(%rdx),%rax
    52ac:	48 63 7a 10          	movslq 0x10(%rdx),%rdi
    52b0:	48 39 f8             	cmp    %rdi,%rax
    52b3:	7d 41                	jge    52f6 <barriered_work+0xd6>
    52b5:	4c 8b 02             	mov    (%rdx),%r8
    52b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    52c0:	48 8b 43 10          	mov    0x10(%rbx),%rax
    52c4:	48 83 c0 01          	add    $0x1,%rax
    52c8:	48 89 43 10          	mov    %rax,0x10(%rbx)
    52cc:	48 8b 43 70          	mov    0x70(%rbx),%rax
    52d0:	48 83 44 08 10 01    	addq   $0x1,0x10(%rax,%rcx,1)
    52d6:	48 8b 42 08          	mov    0x8(%rdx),%rax
    52da:	48 8d 70 01          	lea    0x1(%rax),%rsi
    52de:	48 89 72 08          	mov    %rsi,0x8(%rdx)
    52e2:	48 8b b3 88 00 00 00 	mov    0x88(%rbx),%rsi
    52e9:	49 89 34 c0          	mov    %rsi,(%r8,%rax,8)
    52ed:	48 8b 42 08          	mov    0x8(%rdx),%rax
    52f1:	48 39 f8             	cmp    %rdi,%rax
    52f4:	7c ca                	jl     52c0 <barriered_work+0xa0>
    52f6:	8b 43 3c             	mov    0x3c(%rbx),%eax
    52f9:	49 83 c1 01          	add    $0x1,%r9
    52fd:	44 39 c8             	cmp    %r9d,%eax
    5300:	7f 8e                	jg     5290 <barriered_work+0x70>
    5302:	e9 68 ff ff ff       	jmp    526f <barriered_work+0x4f>
    5307:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    5310:	e8 1b fe ff ff       	call   5130 <receive>
    5315:	8b 3b                	mov    (%rbx),%edi
    5317:	8b 43 3c             	mov    0x3c(%rbx),%eax
    531a:	85 c0                	test   %eax,%eax
    531c:	0f 8e b4 00 00 00    	jle    53d6 <barriered_work+0x1b6>
    5322:	48 63 c7             	movslq %edi,%rax
    5325:	45 31 d2             	xor    %r10d,%r10d
    5328:	45 31 e4             	xor    %r12d,%r12d
    532b:	83 c7 01             	add    $0x1,%edi
    532e:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    5332:	48 8d 2c 50          	lea    (%rax,%rdx,2),%rbp
    5336:	48 c1 e5 03          	shl    $0x3,%rbp
    533a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5340:	8b 43 3c             	mov    0x3c(%rbx),%eax
    5343:	4d 89 e3             	mov    %r12,%r11
    5346:	31 f6                	xor    %esi,%esi
    5348:	31 c9                	xor    %ecx,%ecx
    534a:	49 c1 e3 05          	shl    $0x5,%r11
    534e:	85 c0                	test   %eax,%eax
    5350:	7e 6d                	jle    53bf <barriered_work+0x19f>
    5352:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5358:	44 8b 6b 3c          	mov    0x3c(%rbx),%r13d
    535c:	48 8b 43 30          	mov    0x30(%rbx),%rax
    5360:	48 8b 40 10          	mov    0x10(%rax),%rax
    5364:	4a 8b 54 10 20       	mov    0x20(%rax,%r10,1),%rdx
    5369:	48 01 ea             	add    %rbp,%rdx
    536c:	4c 8b 42 70          	mov    0x70(%rdx),%r8
    5370:	48 8b 43 30          	mov    0x30(%rbx),%rax
    5374:	4c 8b 48 10          	mov    0x10(%rax),%r9
    5378:	89 f8                	mov    %edi,%eax
    537a:	99                   	cltd
    537b:	41 f7 fd             	idiv   %r13d
    537e:	89 d0                	mov    %edx,%eax
    5380:	f7 d8                	neg    %eax
    5382:	0f 49 d0             	cmovns %eax,%edx
    5385:	48 63 d2             	movslq %edx,%rdx
    5388:	48 8d 04 d2          	lea    (%rdx,%rdx,8),%rax
    538c:	48 8d 14 42          	lea    (%rdx,%rax,2),%rdx
    5390:	49 8b 44 31 20       	mov    0x20(%r9,%rsi,1),%rax
    5395:	48 81 c6 98 00 00 00 	add    $0x98,%rsi
    539c:	48 8d 04 d0          	lea    (%rax,%rdx,8),%rax
    53a0:	48 89 ca             	mov    %rcx,%rdx
    53a3:	48 83 c1 01          	add    $0x1,%rcx
    53a7:	48 c1 e2 05          	shl    $0x5,%rdx
    53ab:	48 8b 40 70          	mov    0x70(%rax),%rax
    53af:	49 8b 54 10 08       	mov    0x8(%r8,%rdx,1),%rdx
    53b4:	4a 89 14 18          	mov    %rdx,(%rax,%r11,1)
    53b8:	8b 43 3c             	mov    0x3c(%rbx),%eax
    53bb:	39 c8                	cmp    %ecx,%eax
    53bd:	7f 99                	jg     5358 <barriered_work+0x138>
    53bf:	8b 43 3c             	mov    0x3c(%rbx),%eax
    53c2:	49 83 c4 01          	add    $0x1,%r12
    53c6:	49 81 c2 98 00 00 00 	add    $0x98,%r10
    53cd:	44 39 e0             	cmp    %r12d,%eax
    53d0:	0f 8f 6a ff ff ff    	jg     5340 <barriered_work+0x120>
    53d6:	0f ae f0             	mfence
    53d9:	48 8b 73 50          	mov    0x50(%rbx),%rsi
    53dd:	48 8b 43 60          	mov    0x60(%rbx),%rax
    53e1:	31 ff                	xor    %edi,%edi
    53e3:	48 c1 e0 05          	shl    $0x5,%rax
    53e7:	48 01 c6             	add    %rax,%rsi
    53ea:	e8 01 cf ff ff       	call   22f0 <clock_gettime@plt>
    53ef:	48 8b 43 30          	mov    0x30(%rbx),%rax
    53f3:	48 8b 40 30          	mov    0x30(%rax),%rax
    53f7:	8b 78 10             	mov    0x10(%rax),%edi
    53fa:	8d 6f 01             	lea    0x1(%rdi),%ebp
    53fd:	89 68 10             	mov    %ebp,0x10(%rax)
    5400:	8b 43 48             	mov    0x48(%rbx),%eax
    5403:	83 f8 01             	cmp    $0x1,%eax
    5406:	75 4d                	jne    5455 <barriered_work+0x235>
    5408:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5410:	48 8b 43 10          	mov    0x10(%rbx),%rax
    5414:	48 83 c0 01          	add    $0x1,%rax
    5418:	48 89 43 10          	mov    %rax,0x10(%rbx)
    541c:	48 8b 4b 28          	mov    0x28(%rbx),%rcx
    5420:	48 8b 73 30          	mov    0x30(%rbx),%rsi
    5424:	48 63 43 38          	movslq 0x38(%rbx),%rax
    5428:	48 63 13             	movslq (%rbx),%rdx
    542b:	48 8d 3c c0          	lea    (%rax,%rax,8),%rdi
    542f:	48 8d 04 78          	lea    (%rax,%rdi,2),%rax
    5433:	48 8b 7e 10          	mov    0x10(%rsi),%rdi
    5437:	48 8d 34 d2          	lea    (%rdx,%rdx,8),%rsi
    543b:	48 8d 14 72          	lea    (%rdx,%rsi,2),%rdx
    543f:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    5443:	48 8b 40 20          	mov    0x20(%rax),%rax
    5447:	48 8d 3c d0          	lea    (%rax,%rdx,8),%rdi
    544b:	ff d1                	call   *%rcx
    544d:	8b 43 48             	mov    0x48(%rbx),%eax
    5450:	83 f8 01             	cmp    $0x1,%eax
    5453:	74 bb                	je     5410 <barriered_work+0x1f0>
    5455:	48 8b 43 30          	mov    0x30(%rbx),%rax
    5459:	48 8b 40 30          	mov    0x30(%rax),%rax
    545d:	3b 68 10             	cmp    0x10(%rax),%ebp
    5460:	75 32                	jne    5494 <barriered_work+0x274>
    5462:	48 8b 53 50          	mov    0x50(%rbx),%rdx
    5466:	48 8b 43 60          	mov    0x60(%rbx),%rax
    546a:	31 ff                	xor    %edi,%edi
    546c:	48 c1 e0 05          	shl    $0x5,%rax
    5470:	48 8d 74 02 10       	lea    0x10(%rdx,%rax,1),%rsi
    5475:	e8 76 ce ff ff       	call   22f0 <clock_gettime@plt>
    547a:	48 8b 43 60          	mov    0x60(%rbx),%rax
    547e:	48 8b 4b 58          	mov    0x58(%rbx),%rcx
    5482:	48 83 c0 01          	add    $0x1,%rax
    5486:	48 99                	cqto
    5488:	48 f7 f9             	idiv   %rcx
    548b:	48 89 53 60          	mov    %rdx,0x60(%rbx)
    548f:	e9 db fd ff ff       	jmp    526f <barriered_work+0x4f>
    5494:	48 8d 3d 69 0d 00 00 	lea    0xd69(%rip),%rdi        # 6204 <_IO_stdin_used+0x204>
    549b:	e8 30 ce ff ff       	call   22d0 <puts@plt>
    54a0:	eb c0                	jmp    5462 <barriered_work+0x242>
    54a2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    54ad:	0f 1f 00             	nopl   (%rax)

00000000000054b0 <barriered_work_ingest>:
    54b0:	f3 0f 1e fa          	endbr64
    54b4:	48 83 ec 08          	sub    $0x8,%rsp
    54b8:	48 8b 47 30          	mov    0x30(%rdi),%rax
    54bc:	48 8b 40 38          	mov    0x38(%rax),%rax
    54c0:	8b 00                	mov    (%rax),%eax
    54c2:	85 c0                	test   %eax,%eax
    54c4:	7e 57                	jle    551d <barriered_work_ingest+0x6d>
    54c6:	31 c0                	xor    %eax,%eax
    54c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    54d0:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
    54d4:	48 89 c2             	mov    %rax,%rdx
    54d7:	48 c1 e2 04          	shl    $0x4,%rdx
    54db:	48 8b 49 38          	mov    0x38(%rcx),%rcx
    54df:	48 8b 71 08          	mov    0x8(%rcx),%rsi
    54e3:	48 01 d6             	add    %rdx,%rsi
    54e6:	8b 4e 08             	mov    0x8(%rsi),%ecx
    54e9:	83 f9 01             	cmp    $0x1,%ecx
    54ec:	75 1f                	jne    550d <barriered_work_ingest+0x5d>
    54ee:	48 8b 4f 68          	mov    0x68(%rdi),%rcx
    54f2:	48 83 c1 01          	add    $0x1,%rcx
    54f6:	48 89 4f 68          	mov    %rcx,0x68(%rdi)
    54fa:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
    54fe:	48 8b 49 38          	mov    0x38(%rcx),%rcx
    5502:	48 03 51 08          	add    0x8(%rcx),%rdx
    5506:	c7 42 08 00 00 00 00 	movl   $0x0,0x8(%rdx)
    550d:	48 8b 57 30          	mov    0x30(%rdi),%rdx
    5511:	48 83 c0 01          	add    $0x1,%rax
    5515:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    5519:	39 02                	cmp    %eax,(%rdx)
    551b:	7f b3                	jg     54d0 <barriered_work_ingest+0x20>
    551d:	0f ae f0             	mfence
    5520:	e8 fb fc ff ff       	call   5220 <barriered_work>
    5525:	31 c0                	xor    %eax,%eax
    5527:	48 83 c4 08          	add    $0x8,%rsp
    552b:	c3                   	ret
    552c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005530 <barriered_nulltask>:
    5530:	f3 0f 1e fa          	endbr64
    5534:	31 c0                	xor    %eax,%eax
    5536:	c3                   	ret
    5537:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005540 <barriered_steal>:
    5540:	f3 0f 1e fa          	endbr64
    5544:	31 c0                	xor    %eax,%eax
    5546:	c3                   	ret
    5547:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005550 <after>:
    5550:	f3 0f 1e fa          	endbr64
    5554:	31 c0                	xor    %eax,%eax
    5556:	48 39 d7             	cmp    %rdx,%rdi
    5559:	7e 08                	jle    5563 <after+0x13>
    555b:	31 c0                	xor    %eax,%eax
    555d:	48 39 ce             	cmp    %rcx,%rsi
    5560:	0f 9f c0             	setg   %al
    5563:	c3                   	ret
    5564:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    556f:	90                   	nop

0000000000005570 <within>:
    5570:	f3 0f 1e fa          	endbr64
    5574:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5579:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    557e:	31 c0                	xor    %eax,%eax
    5580:	48 39 d7             	cmp    %rdx,%rdi
    5583:	7f 18                	jg     559d <within+0x2d>
    5585:	4d 39 d8             	cmp    %r11,%r8
    5588:	0f 9e c2             	setle  %dl
    558b:	48 39 ce             	cmp    %rcx,%rsi
    558e:	0f 9e c0             	setle  %al
    5591:	21 c2                	and    %eax,%edx
    5593:	31 c0                	xor    %eax,%eax
    5595:	4d 39 d1             	cmp    %r10,%r9
    5598:	0f 9e c0             	setle  %al
    559b:	21 d0                	and    %edx,%eax
    559d:	c3                   	ret
    559e:	66 90                	xchg   %ax,%ax

00000000000055a0 <overlap>:
    55a0:	f3 0f 1e fa          	endbr64
    55a4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    55a9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    55ae:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    55b3:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    55b8:	4c 8b 4c 24 38       	mov    0x38(%rsp),%r9
    55bd:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
    55c2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    55c7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    55cc:	48 39 fe             	cmp    %rdi,%rsi
    55cf:	7d 2f                	jge    5600 <overlap+0x60>
    55d1:	48 39 ca             	cmp    %rcx,%rdx
    55d4:	7d 62                	jge    5638 <overlap+0x98>
    55d6:	4d 39 da             	cmp    %r11,%r10
    55d9:	7e 0e                	jle    55e9 <overlap+0x49>
    55db:	b8 01 00 00 00       	mov    $0x1,%eax
    55e0:	4d 39 c1             	cmp    %r8,%r9
    55e3:	0f 8f 7f 00 00 00    	jg     5668 <overlap+0xc8>
    55e9:	31 c0                	xor    %eax,%eax
    55eb:	4d 39 c1             	cmp    %r8,%r9
    55ee:	7c 4c                	jl     563c <overlap+0x9c>
    55f0:	31 c0                	xor    %eax,%eax
    55f2:	4d 39 da             	cmp    %r11,%r10
    55f5:	0f 9d c0             	setge  %al
    55f8:	c3                   	ret
    55f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5600:	7e 4e                	jle    5650 <overlap+0xb0>
    5602:	48 39 ca             	cmp    %rcx,%rdx
    5605:	7f 39                	jg     5640 <overlap+0xa0>
    5607:	75 31                	jne    563a <overlap+0x9a>
    5609:	4d 39 c1             	cmp    %r8,%r9
    560c:	7f 2c                	jg     563a <overlap+0x9a>
    560e:	b8 01 00 00 00       	mov    $0x1,%eax
    5613:	4d 39 da             	cmp    %r11,%r10
    5616:	7e 24                	jle    563c <overlap+0x9c>
    5618:	48 39 ca             	cmp    %rcx,%rdx
    561b:	0f 94 c2             	sete   %dl
    561e:	48 39 fe             	cmp    %rdi,%rsi
    5621:	0f 94 c0             	sete   %al
    5624:	21 c2                	and    %eax,%edx
    5626:	31 c0                	xor    %eax,%eax
    5628:	4d 39 c1             	cmp    %r8,%r9
    562b:	0f 94 c0             	sete   %al
    562e:	21 d0                	and    %edx,%eax
    5630:	c3                   	ret
    5631:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5638:	74 af                	je     55e9 <overlap+0x49>
    563a:	31 c0                	xor    %eax,%eax
    563c:	c3                   	ret
    563d:	0f 1f 00             	nopl   (%rax)
    5640:	4d 39 c1             	cmp    %r8,%r9
    5643:	7d c4                	jge    5609 <overlap+0x69>
    5645:	b8 01 00 00 00       	mov    $0x1,%eax
    564a:	4d 39 da             	cmp    %r11,%r10
    564d:	7d ba                	jge    5609 <overlap+0x69>
    564f:	c3                   	ret
    5650:	48 39 ca             	cmp    %rcx,%rdx
    5653:	7c 94                	jl     55e9 <overlap+0x49>
    5655:	4d 39 c1             	cmp    %r8,%r9
    5658:	7e b4                	jle    560e <overlap+0x6e>
    565a:	48 39 ca             	cmp    %rcx,%rdx
    565d:	74 91                	je     55f0 <overlap+0x50>
    565f:	eb d9                	jmp    563a <overlap+0x9a>
    5661:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5668:	c3                   	ret
    5669:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005670 <verify>:
    5670:	f3 0f 1e fa          	endbr64
    5674:	85 f6                	test   %esi,%esi
    5676:	0f 8e 0d 03 00 00    	jle    5989 <verify+0x319>
    567c:	41 57                	push   %r15
    567e:	45 31 ff             	xor    %r15d,%r15d
    5681:	41 56                	push   %r14
    5683:	41 89 f6             	mov    %esi,%r14d
    5686:	41 55                	push   %r13
    5688:	4c 8d 6f 20          	lea    0x20(%rdi),%r13
    568c:	41 54                	push   %r12
    568e:	55                   	push   %rbp
    568f:	53                   	push   %rbx
    5690:	48 83 ec 48          	sub    $0x48,%rsp
    5694:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
    5699:	4c 89 6c 24 08       	mov    %r13,0x8(%rsp)
    569e:	45 31 e4             	xor    %r12d,%r12d
    56a1:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    56a6:	45 39 e7             	cmp    %r12d,%r15d
    56a9:	0f 84 37 02 00 00    	je     58e6 <verify+0x276>
    56af:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    56b4:	8b 50 08             	mov    0x8(%rax),%edx
    56b7:	85 d2                	test   %edx,%edx
    56b9:	0f 8e 27 02 00 00    	jle    58e6 <verify+0x276>
    56bf:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    56c8:	31 ed                	xor    %ebp,%ebp
    56ca:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    56cf:	44 89 fa             	mov    %r15d,%edx
    56d2:	48 8d 35 3b 0b 00 00 	lea    0xb3b(%rip),%rsi        # 6214 <_IO_stdin_used+0x214>
    56d9:	bf 01 00 00 00       	mov    $0x1,%edi
    56de:	31 c0                	xor    %eax,%eax
    56e0:	e8 4b cd ff ff       	call   2430 <__printf_chk@plt>
    56e5:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    56ea:	8b 40 08             	mov    0x8(%rax),%eax
    56ed:	85 c0                	test   %eax,%eax
    56ef:	0f 8e d2 01 00 00    	jle    58c7 <verify+0x257>
    56f5:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    56fa:	89 6c 24 34          	mov    %ebp,0x34(%rsp)
    56fe:	45 31 e4             	xor    %r12d,%r12d
    5701:	44 89 7c 24 38       	mov    %r15d,0x38(%rsp)
    5706:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    570b:	44 89 74 24 3c       	mov    %r14d,0x3c(%rsp)
    5710:	4c 03 28             	add    (%rax),%r13
    5713:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5718:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    571d:	4b 8d 04 e4          	lea    (%r12,%r12,8),%rax
    5721:	49 8b 4d 60          	mov    0x60(%r13),%rcx
    5725:	48 8d 35 fd 0a 00 00 	lea    0xafd(%rip),%rsi        # 6229 <_IO_stdin_used+0x229>
    572c:	49 8d 2c 44          	lea    (%r12,%rax,2),%rbp
    5730:	bf 01 00 00 00       	mov    $0x1,%edi
    5735:	48 8b 03             	mov    (%rbx),%rax
    5738:	48 c1 e5 03          	shl    $0x3,%rbp
    573c:	48 01 e8             	add    %rbp,%rax
    573f:	48 8b 50 60          	mov    0x60(%rax),%rdx
    5743:	31 c0                	xor    %eax,%eax
    5745:	e8 e6 cc ff ff       	call   2430 <__printf_chk@plt>
    574a:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    574f:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    5754:	4c 03 28             	add    (%rax),%r13
    5757:	49 8b 45 60          	mov    0x60(%r13),%rax
    575b:	48 85 c0             	test   %rax,%rax
    575e:	0f 8e 42 01 00 00    	jle    58a6 <verify+0x236>
    5764:	48 8b 13             	mov    (%rbx),%rdx
    5767:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
    576c:	45 31 ff             	xor    %r15d,%r15d
    576f:	48 01 ea             	add    %rbp,%rdx
    5772:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5778:	48 8b 42 60          	mov    0x60(%rdx),%rax
    577c:	4d 89 fc             	mov    %r15,%r12
    577f:	31 db                	xor    %ebx,%ebx
    5781:	49 c1 e4 05          	shl    $0x5,%r12
    5785:	48 85 c0             	test   %rax,%rax
    5788:	7f 37                	jg     57c1 <verify+0x151>
    578a:	e9 01 01 00 00       	jmp    5890 <verify+0x220>
    578f:	90                   	nop
    5790:	48 39 f1             	cmp    %rsi,%rcx
    5793:	0f 8d 6f 01 00 00    	jge    5908 <verify+0x298>
    5799:	4d 39 da             	cmp    %r11,%r10
    579c:	7e 09                	jle    57a7 <verify+0x137>
    579e:	49 39 c6             	cmp    %rax,%r14
    57a1:	0f 8c 81 00 00 00    	jl     5828 <verify+0x1b8>
    57a7:	4d 39 da             	cmp    %r11,%r10
    57aa:	0f 8d 9b 01 00 00    	jge    594b <verify+0x2db>
    57b0:	48 8b 42 60          	mov    0x60(%rdx),%rax
    57b4:	48 83 c3 01          	add    $0x1,%rbx
    57b8:	48 39 d8             	cmp    %rbx,%rax
    57bb:	0f 8e cf 00 00 00    	jle    5890 <verify+0x220>
    57c1:	48 8b 42 50          	mov    0x50(%rdx),%rax
    57c5:	49 89 d9             	mov    %rbx,%r9
    57c8:	49 8b 4d 50          	mov    0x50(%r13),%rcx
    57cc:	49 c1 e1 05          	shl    $0x5,%r9
    57d0:	4c 01 e1             	add    %r12,%rcx
    57d3:	4c 01 c8             	add    %r9,%rax
    57d6:	4c 8b 01             	mov    (%rcx),%r8
    57d9:	48 8b 38             	mov    (%rax),%rdi
    57dc:	48 8b 71 08          	mov    0x8(%rcx),%rsi
    57e0:	4c 8b 59 10          	mov    0x10(%rcx),%r11
    57e4:	4c 8b 71 18          	mov    0x18(%rcx),%r14
    57e8:	4c 8b 50 10          	mov    0x10(%rax),%r10
    57ec:	48 8b 48 08          	mov    0x8(%rax),%rcx
    57f0:	48 8b 40 18          	mov    0x18(%rax),%rax
    57f4:	4c 39 c7             	cmp    %r8,%rdi
    57f7:	7c 97                	jl     5790 <verify+0x120>
    57f9:	0f 8e 31 01 00 00    	jle    5930 <verify+0x2c0>
    57ff:	48 39 f1             	cmp    %rsi,%rcx
    5802:	0f 8f 10 01 00 00    	jg     5918 <verify+0x2a8>
    5808:	75 a6                	jne    57b0 <verify+0x140>
    580a:	4d 39 da             	cmp    %r11,%r10
    580d:	7f a1                	jg     57b0 <verify+0x140>
    580f:	49 39 c6             	cmp    %rax,%r14
    5812:	7d 14                	jge    5828 <verify+0x1b8>
    5814:	4c 39 c7             	cmp    %r8,%rdi
    5817:	75 97                	jne    57b0 <verify+0x140>
    5819:	48 39 f1             	cmp    %rsi,%rcx
    581c:	75 92                	jne    57b0 <verify+0x140>
    581e:	4d 39 da             	cmp    %r11,%r10
    5821:	75 8d                	jne    57b0 <verify+0x140>
    5823:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5828:	48 8b 72 50          	mov    0x50(%rdx),%rsi
    582c:	49 8b 45 50          	mov    0x50(%r13),%rax
    5830:	bf 01 00 00 00       	mov    $0x1,%edi
    5835:	48 83 c3 01          	add    $0x1,%rbx
    5839:	48 8b 4a 50          	mov    0x50(%rdx),%rcx
    583d:	49 8b 55 50          	mov    0x50(%r13),%rdx
    5841:	4e 8b 44 20 08       	mov    0x8(%rax,%r12,1),%r8
    5846:	31 c0                	xor    %eax,%eax
    5848:	4a 8b 4c 09 10       	mov    0x10(%rcx,%r9,1),%rcx
    584d:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    5851:	4e 8b 4c 0e 18       	mov    0x18(%rsi,%r9,1),%r9
    5856:	48 8d 35 43 0c 00 00 	lea    0xc43(%rip),%rsi        # 64a0 <_IO_stdin_used+0x4a0>
    585d:	e8 ce cb ff ff       	call   2430 <__printf_chk@plt>
    5862:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5867:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    586c:	4c 03 28             	add    (%rax),%r13
    586f:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5874:	48 8b 10             	mov    (%rax),%rdx
    5877:	48 01 ea             	add    %rbp,%rdx
    587a:	48 8b 42 60          	mov    0x60(%rdx),%rax
    587e:	48 39 d8             	cmp    %rbx,%rax
    5881:	0f 8f 3a ff ff ff    	jg     57c1 <verify+0x151>
    5887:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    5890:	49 8b 45 60          	mov    0x60(%r13),%rax
    5894:	49 83 c7 01          	add    $0x1,%r15
    5898:	4c 39 f8             	cmp    %r15,%rax
    589b:	0f 8f d7 fe ff ff    	jg     5778 <verify+0x108>
    58a1:	4c 8b 64 24 20       	mov    0x20(%rsp),%r12
    58a6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    58ab:	49 83 c4 01          	add    $0x1,%r12
    58af:	44 39 60 08          	cmp    %r12d,0x8(%rax)
    58b3:	0f 8f 5f fe ff ff    	jg     5718 <verify+0xa8>
    58b9:	8b 6c 24 34          	mov    0x34(%rsp),%ebp
    58bd:	44 8b 7c 24 38       	mov    0x38(%rsp),%r15d
    58c2:	44 8b 74 24 3c       	mov    0x3c(%rsp),%r14d
    58c7:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    58cc:	83 c5 01             	add    $0x1,%ebp
    58cf:	48 81 44 24 18 98 00 00 00 	addq   $0x98,0x18(%rsp)
    58d8:	39 68 08             	cmp    %ebp,0x8(%rax)
    58db:	0f 8f ee fd ff ff    	jg     56cf <verify+0x5f>
    58e1:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    58e6:	48 81 44 24 08 98 00 00 00 	addq   $0x98,0x8(%rsp)
    58ef:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    58f4:	41 39 c6             	cmp    %eax,%r14d
    58f7:	74 60                	je     5959 <verify+0x2e9>
    58f9:	41 89 c4             	mov    %eax,%r12d
    58fc:	e9 a5 fd ff ff       	jmp    56a6 <verify+0x36>
    5901:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5908:	0f 85 a2 fe ff ff    	jne    57b0 <verify+0x140>
    590e:	e9 94 fe ff ff       	jmp    57a7 <verify+0x137>
    5913:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5918:	49 39 c6             	cmp    %rax,%r14
    591b:	0f 8e e9 fe ff ff    	jle    580a <verify+0x19a>
    5921:	4d 39 da             	cmp    %r11,%r10
    5924:	0f 8d e0 fe ff ff    	jge    580a <verify+0x19a>
    592a:	e9 f9 fe ff ff       	jmp    5828 <verify+0x1b8>
    592f:	90                   	nop
    5930:	48 39 f1             	cmp    %rsi,%rcx
    5933:	0f 8c 6e fe ff ff    	jl     57a7 <verify+0x137>
    5939:	4d 39 da             	cmp    %r11,%r10
    593c:	0f 8e cd fe ff ff    	jle    580f <verify+0x19f>
    5942:	48 39 f1             	cmp    %rsi,%rcx
    5945:	0f 85 65 fe ff ff    	jne    57b0 <verify+0x140>
    594b:	49 39 c6             	cmp    %rax,%r14
    594e:	0f 8f 5c fe ff ff    	jg     57b0 <verify+0x140>
    5954:	e9 cf fe ff ff       	jmp    5828 <verify+0x1b8>
    5959:	48 81 44 24 10 98 00 00 00 	addq   $0x98,0x10(%rsp)
    5962:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    5967:	41 8d 47 01          	lea    0x1(%r15),%eax
    596b:	45 39 e7             	cmp    %r12d,%r15d
    596e:	74 08                	je     5978 <verify+0x308>
    5970:	41 89 c7             	mov    %eax,%r15d
    5973:	e9 21 fd ff ff       	jmp    5699 <verify+0x29>
    5978:	48 83 c4 48          	add    $0x48,%rsp
    597c:	31 c0                	xor    %eax,%eax
    597e:	5b                   	pop    %rbx
    597f:	5d                   	pop    %rbp
    5980:	41 5c                	pop    %r12
    5982:	41 5d                	pop    %r13
    5984:	41 5e                	pop    %r14
    5986:	41 5f                	pop    %r15
    5988:	c3                   	ret
    5989:	31 c0                	xor    %eax,%eax
    598b:	c3                   	ret

Disassembly of section .fini:

000000000000598c <_fini>:
    598c:	f3 0f 1e fa          	endbr64
    5990:	48 83 ec 08          	sub    $0x8,%rsp
    5994:	48 83 c4 08          	add    $0x8,%rsp
    5998:	c3                   	ret
