
barrier-runtime-server:     file format elf64-x86-64


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
    2566:	48 8d 3d 83 3e 00 00 	lea    0x3e83(%rip),%rdi        # 63f0 <_IO_stdin_used+0x3f0>
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
    258e:	ba 04 00 00 00       	mov    $0x4,%edx
    2593:	48 8d 35 98 3c 00 00 	lea    0x3c98(%rip),%rsi        # 6232 <_IO_stdin_used+0x232>
    259a:	31 c0                	xor    %eax,%eax
    259c:	bf 01 00 00 00       	mov    $0x1,%edi
    25a1:	e8 8a fe ff ff       	call   2430 <__printf_chk@plt>
    25a6:	ba 0f 27 00 00       	mov    $0x270f,%edx
    25ab:	48 8d 35 6e 3e 00 00 	lea    0x3e6e(%rip),%rsi        # 6420 <_IO_stdin_used+0x420>
    25b2:	31 c0                	xor    %eax,%eax
    25b4:	bf 01 00 00 00       	mov    $0x1,%edi
    25b9:	e8 72 fe ff ff       	call   2430 <__printf_chk@plt>
    25be:	ba 0f 27 00 00       	mov    $0x270f,%edx
    25c3:	48 8d 35 86 3e 00 00 	lea    0x3e86(%rip),%rsi        # 6450 <_IO_stdin_used+0x450>
    25ca:	31 c0                	xor    %eax,%eax
    25cc:	bf 01 00 00 00       	mov    $0x1,%edi
    25d1:	e8 5a fe ff ff       	call   2430 <__printf_chk@plt>
    25d6:	be 18 00 00 00       	mov    $0x18,%esi
    25db:	bf 01 00 00 00       	mov    $0x1,%edi
    25e0:	e8 9b fd ff ff       	call   2380 <calloc@plt>
    25e5:	be 78 00 00 00       	mov    $0x78,%esi
    25ea:	bf 09 00 00 00       	mov    $0x9,%edi
    25ef:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    25f4:	e8 87 fd ff ff       	call   2380 <calloc@plt>
    25f9:	be 10 00 00 00       	mov    $0x10,%esi
    25fe:	bf 03 00 00 00       	mov    $0x3,%edi
    2603:	49 89 c4             	mov    %rax,%r12
    2606:	e8 75 fd ff ff       	call   2380 <calloc@plt>
    260b:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    2610:	48 8d 58 30          	lea    0x30(%rax),%rbx
    2614:	48 89 c5             	mov    %rax,%rbp
    2617:	49 89 c5             	mov    %rax,%r13
    261a:	c7 45 00 0f 27 00 00 	movl   $0x270f,0x0(%rbp)
    2621:	be 10 00 00 00       	mov    $0x10,%esi
    2626:	bf 0f 27 00 00       	mov    $0x270f,%edi
    262b:	e8 50 fd ff ff       	call   2380 <calloc@plt>
    2630:	48 89 45 08          	mov    %rax,0x8(%rbp)
    2634:	48 8d 90 f0 70 02 00 	lea    0x270f0(%rax),%rdx
    263b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    2640:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
    2647:	48 83 c0 10          	add    $0x10,%rax
    264b:	48 39 d0             	cmp    %rdx,%rax
    264e:	75 f0                	jne    2640 <main+0xe0>
    2650:	48 83 c5 10          	add    $0x10,%rbp
    2654:	48 39 dd             	cmp    %rbx,%rbp
    2657:	75 c1                	jne    261a <main+0xba>
    2659:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
    2661:	31 d2                	xor    %edx,%edx
    2663:	4d 89 e7             	mov    %r12,%r15
    2666:	4c 89 64 24 38       	mov    %r12,0x38(%rsp)
    266b:	49 89 d0             	mov    %rdx,%r8
    266e:	4c 89 6c 24 40       	mov    %r13,0x40(%rsp)
    2673:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    2678:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    267d:	45 89 07             	mov    %r8d,(%r15)
    2680:	be 98 00 00 00       	mov    $0x98,%esi
    2685:	31 db                	xor    %ebx,%ebx
    2687:	41 c7 47 28 05 00 00 00 	movl   $0x5,0x28(%r15)
    268f:	bf 05 00 00 00       	mov    $0x5,%edi
    2694:	49 89 47 10          	mov    %rax,0x10(%r15)
    2698:	48 8b 05 d9 41 00 00 	mov    0x41d9(%rip),%rax        # 6878 <_IO_stdin_used+0x878>
    269f:	44 89 44 24 20       	mov    %r8d,0x20(%rsp)
    26a4:	49 89 47 18          	mov    %rax,0x18(%r15)
    26a8:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    26ad:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    26b2:	49 89 47 30          	mov    %rax,0x30(%r15)
    26b6:	e8 c5 fc ff ff       	call   2380 <calloc@plt>
    26bb:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    26c0:	49 89 c5             	mov    %rax,%r13
    26c3:	49 89 47 20          	mov    %rax,0x20(%r15)
    26c7:	b8 ab aa aa aa       	mov    $0xaaaaaaab,%eax
    26cc:	44 89 c6             	mov    %r8d,%esi
    26cf:	44 89 44 24 24       	mov    %r8d,0x24(%rsp)
    26d4:	4c 89 ea             	mov    %r13,%rdx
    26d7:	48 0f af f0          	imul   %rax,%rsi
    26db:	48 c1 ee 21          	shr    $0x21,%rsi
    26df:	8d 04 76             	lea    (%rsi,%rsi,2),%eax
    26e2:	44 89 c6             	mov    %r8d,%esi
    26e5:	29 c6                	sub    %eax,%esi
    26e7:	89 74 24 2c          	mov    %esi,0x2c(%rsp)
    26eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    26f0:	4c 63 e3             	movslq %ebx,%r12
    26f3:	4b 8d 04 e4          	lea    (%r12,%r12,8),%rax
    26f7:	49 8d 2c 44          	lea    (%r12,%rax,2),%rbp
    26fb:	8b 44 24 08          	mov    0x8(%rsp),%eax
    26ff:	48 c1 e5 03          	shl    $0x3,%rbp
    2703:	4c 8d 2c 2a          	lea    (%rdx,%rbp,1),%r13
    2707:	39 c3                	cmp    %eax,%ebx
    2709:	0f 84 e9 01 00 00    	je     28f8 <main+0x398>
    270f:	be 20 00 00 00       	mov    $0x20,%esi
    2714:	bf 04 00 00 00       	mov    $0x4,%edi
    2719:	e8 62 fc ff ff       	call   2380 <calloc@plt>
    271e:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    2722:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    2727:	49 89 c6             	mov    %rax,%r14
    272a:	49 89 45 70          	mov    %rax,0x70(%r13)
    272e:	4c 8d a8 80 00 00 00 	lea    0x80(%rax),%r13
    2735:	be 08 00 00 00       	mov    $0x8,%esi
    273a:	bf 0f 27 00 00       	mov    $0x270f,%edi
    273f:	49 83 c6 20          	add    $0x20,%r14
    2743:	e8 38 fc ff ff       	call   2380 <calloc@plt>
    2748:	be 08 00 00 00       	mov    $0x8,%esi
    274d:	bf 0f 27 00 00       	mov    $0x270f,%edi
    2752:	48 89 c5             	mov    %rax,%rbp
    2755:	e8 26 fc ff ff       	call   2380 <calloc@plt>
    275a:	be 18 00 00 00       	mov    $0x18,%esi
    275f:	bf 02 00 00 00       	mov    $0x2,%edi
    2764:	48 89 c3             	mov    %rax,%rbx
    2767:	e8 14 fc ff ff       	call   2380 <calloc@plt>
    276c:	48 8d 70 18          	lea    0x18(%rax),%rsi
    2770:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    2778:	49 89 46 e0          	mov    %rax,-0x20(%r14)
    277c:	49 89 76 e8          	mov    %rsi,-0x18(%r14)
    2780:	48 89 28             	mov    %rbp,(%rax)
    2783:	48 89 58 18          	mov    %rbx,0x18(%rax)
    2787:	48 c7 40 10 0f 27 00 00 	movq   $0x270f,0x10(%rax)
    278f:	48 c7 40 20 00 00 00 00 	movq   $0x0,0x20(%rax)
    2797:	48 c7 40 28 0f 27 00 00 	movq   $0x270f,0x28(%rax)
    279f:	4d 39 ee             	cmp    %r13,%r14
    27a2:	75 91                	jne    2735 <main+0x1d5>
    27a4:	be 01 00 00 00       	mov    $0x1,%esi
    27a9:	bf 00 01 00 00       	mov    $0x100,%edi
    27ae:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    27b2:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    27b7:	e8 c4 fb ff ff       	call   2380 <calloc@plt>
    27bc:	bf 18 00 00 00       	mov    $0x18,%edi
    27c1:	49 89 c5             	mov    %rax,%r13
    27c4:	e8 27 fc ff ff       	call   23f0 <malloc@plt>
    27c9:	44 8b 74 24 20       	mov    0x20(%rsp),%r14d
    27ce:	4c 89 ef             	mov    %r13,%rdi
    27d1:	41 89 d9             	mov    %ebx,%r9d
    27d4:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    27d9:	48 8d 0d 98 3c 00 00 	lea    0x3c98(%rip),%rcx        # 6478 <_IO_stdin_used+0x478>
    27e0:	ba 00 01 00 00       	mov    $0x100,%edx
    27e5:	31 c0                	xor    %eax,%eax
    27e7:	45 89 f0             	mov    %r14d,%r8d
    27ea:	be 01 00 00 00       	mov    $0x1,%esi
    27ef:	e8 0c fd ff ff       	call   2500 <__sprintf_chk@plt>
    27f4:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    27f9:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    27fe:	be 20 00 00 00       	mov    $0x20,%esi
    2803:	49 8b 57 20          	mov    0x20(%r15),%rdx
    2807:	4d 89 2a             	mov    %r13,(%r10)
    280a:	44 8d 6b 01          	lea    0x1(%rbx),%r13d
    280e:	49 89 42 08          	mov    %rax,0x8(%r10)
    2812:	44 89 e8             	mov    %r13d,%eax
    2815:	4d 89 62 10          	mov    %r12,0x10(%r10)
    2819:	83 e0 03             	and    $0x3,%eax
    281c:	4c 8d 24 2a          	lea    (%rdx,%rbp,1),%r12
    2820:	41 89 84 24 90 00 00 00 	mov    %eax,0x90(%r12)
    2828:	4d 89 94 24 88 00 00 00 	mov    %r10,0x88(%r12)
    2830:	41 c7 84 24 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%r12)
    283c:	49 c7 44 24 58 3f 42 0f 00 	movq   $0xf423f,0x58(%r12)
    2845:	49 8b 7c 24 58       	mov    0x58(%r12),%rdi
    284a:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
    284f:	e8 2c fb ff ff       	call   2380 <calloc@plt>
    2854:	83 fb 03             	cmp    $0x3,%ebx
    2857:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    285c:	49 89 44 24 50       	mov    %rax,0x50(%r12)
    2861:	49 c7 44 24 60 00 00 00 00 	movq   $0x0,0x60(%r12)
    286a:	45 89 74 24 38       	mov    %r14d,0x38(%r12)
    286f:	4d 89 7c 24 30       	mov    %r15,0x30(%r12)
    2874:	41 c7 44 24 40 01 00 00 00 	movl   $0x1,0x40(%r12)
    287d:	41 c7 44 24 08 00 00 00 00 	movl   $0x0,0x8(%r12)
    2886:	41 c7 44 24 3c 04 00 00 00 	movl   $0x4,0x3c(%r12)
    288f:	41 c7 44 24 44 05 00 00 00 	movl   $0x5,0x44(%r12)
    2898:	41 c7 84 24 84 00 00 00 04 00 00 00 	movl   $0x4,0x84(%r12)
    28a4:	41 89 1c 24          	mov    %ebx,(%r12)
    28a8:	74 36                	je     28e0 <main+0x380>
    28aa:	8b 44 24 24          	mov    0x24(%rsp),%eax
    28ae:	39 c3                	cmp    %eax,%ebx
    28b0:	75 12                	jne    28c4 <main+0x364>
    28b2:	83 7c 24 28 02       	cmpl   $0x2,0x28(%rsp)
    28b7:	7f 0b                	jg     28c4 <main+0x364>
    28b9:	83 7c 24 2c 01       	cmpl   $0x1,0x2c(%rsp)
    28be:	0f 84 8c 06 00 00    	je     2f50 <main+0x9f0>
    28c4:	48 8d 05 f5 25 00 00 	lea    0x25f5(%rip),%rax        # 4ec0 <barriered_work>
    28cb:	49 89 44 24 20       	mov    %rax,0x20(%r12)
    28d0:	41 83 fd 05          	cmp    $0x5,%r13d
    28d4:	74 3a                	je     2910 <main+0x3b0>
    28d6:	44 89 eb             	mov    %r13d,%ebx
    28d9:	e9 12 fe ff ff       	jmp    26f0 <main+0x190>
    28de:	66 90                	xchg   %ax,%ax
    28e0:	48 8d 05 d9 25 00 00 	lea    0x25d9(%rip),%rax        # 4ec0 <barriered_work>
    28e7:	41 bd 04 00 00 00    	mov    $0x4,%r13d
    28ed:	49 89 44 24 20       	mov    %rax,0x20(%r12)
    28f2:	eb e2                	jmp    28d6 <main+0x376>
    28f4:	0f 1f 40 00          	nopl   0x0(%rax)
    28f8:	48 8d 05 a1 07 00 00 	lea    0x7a1(%rip),%rax        # 30a0 <do_protected_write>
    28ff:	49 89 45 28          	mov    %rax,0x28(%r13)
    2903:	e9 07 fe ff ff       	jmp    270f <main+0x1af>
    2908:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    2910:	48 8d 05 c9 07 00 00 	lea    0x7c9(%rip),%rax        # 30e0 <barriered_reset>
    2917:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    291c:	48 89 82 80 02 00 00 	mov    %rax,0x280(%rdx)
    2923:	8b 44 24 20          	mov    0x20(%rsp),%eax
    2927:	49 83 c0 01          	add    $0x1,%r8
    292b:	4c 89 ba 90 02 00 00 	mov    %r15,0x290(%rdx)
    2932:	49 83 c7 78          	add    $0x78,%r15
    2936:	c7 82 a0 02 00 00 01 00 00 00 	movl   $0x1,0x2a0(%rdx)
    2940:	c7 82 68 02 00 00 00 00 00 00 	movl   $0x0,0x268(%rdx)
    294a:	c7 82 60 02 00 00 04 00 00 00 	movl   $0x4,0x260(%rdx)
    2954:	c7 82 9c 02 00 00 04 00 00 00 	movl   $0x4,0x29c(%rdx)
    295e:	89 82 98 02 00 00    	mov    %eax,0x298(%rdx)
    2964:	c7 82 e4 02 00 00 04 00 00 00 	movl   $0x4,0x2e4(%rdx)
    296e:	c7 82 a4 02 00 00 05 00 00 00 	movl   $0x5,0x2a4(%rdx)
    2978:	49 83 f8 09          	cmp    $0x9,%r8
    297c:	0f 85 f6 fc ff ff    	jne    2678 <main+0x118>
    2982:	4c 8b 64 24 38       	mov    0x38(%rsp),%r12
    2987:	be 38 00 00 00       	mov    $0x38,%esi
    298c:	bf 09 00 00 00       	mov    $0x9,%edi
    2991:	45 31 f6             	xor    %r14d,%r14d
    2994:	49 8d 84 24 58 02 00 00 	lea    0x258(%r12),%rax
    299c:	4d 89 e7             	mov    %r12,%r15
    299f:	4d 89 a4 24 68 02 00 00 	mov    %r12,0x268(%r12)
    29a7:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    29ac:	49 8b 44 24 20       	mov    0x20(%r12),%rax
    29b1:	41 c7 84 24 70 02 00 00 04 00 00 00 	movl   $0x4,0x270(%r12)
    29bd:	41 c7 84 24 58 02 00 00 05 00 00 00 	movl   $0x5,0x258(%r12)
    29c9:	41 c7 84 24 80 02 00 00 05 00 00 00 	movl   $0x5,0x280(%r12)
    29d5:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    29dc:	49 8b 84 24 98 00 00 00 	mov    0x98(%r12),%rax
    29e4:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    29eb:	49 8b 84 24 10 01 00 00 	mov    0x110(%r12),%rax
    29f3:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    29fa:	49 8b 84 24 88 01 00 00 	mov    0x188(%r12),%rax
    2a02:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    2a09:	e8 72 f9 ff ff       	call   2380 <calloc@plt>
    2a0e:	be 38 00 00 00       	mov    $0x38,%esi
    2a13:	bf 09 00 00 00       	mov    $0x9,%edi
    2a18:	48 89 c3             	mov    %rax,%rbx
    2a1b:	e8 60 f9 ff ff       	call   2380 <calloc@plt>
    2a20:	be 38 00 00 00       	mov    $0x38,%esi
    2a25:	bf 09 00 00 00       	mov    $0x9,%edi
    2a2a:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2a2f:	e8 4c f9 ff ff       	call   2380 <calloc@plt>
    2a34:	be 08 00 00 00       	mov    $0x8,%esi
    2a39:	bf 09 00 00 00       	mov    $0x9,%edi
    2a3e:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2a43:	e8 38 f9 ff ff       	call   2380 <calloc@plt>
    2a48:	4d 89 a4 24 f0 01 00 00 	mov    %r12,0x1f0(%r12)
    2a50:	49 8d 8c 24 e0 01 00 00 	lea    0x1e0(%r12),%rcx
    2a58:	48 8d b3 e0 00 00 00 	lea    0xe0(%rbx),%rsi
    2a5f:	41 c7 84 24 e4 01 00 00 00 00 00 00 	movl   $0x0,0x1e4(%r12)
    2a6b:	48 89 c5             	mov    %rax,%rbp
    2a6e:	48 8d 78 20          	lea    0x20(%rax),%rdi
    2a72:	48 8d 15 57 09 00 00 	lea    0x957(%rip),%rdx        # 33d0 <timer_thread>
    2a79:	41 c7 84 24 0c 02 00 00 01 00 00 00 	movl   $0x1,0x20c(%r12)
    2a85:	49 89 ed             	mov    %rbp,%r13
    2a88:	41 c7 84 24 08 02 00 00 05 00 00 00 	movl   $0x5,0x208(%r12)
    2a94:	41 c7 84 24 f8 01 00 00 04 00 00 00 	movl   $0x4,0x1f8(%r12)
    2aa0:	41 c7 84 24 e0 01 00 00 00 00 00 00 	movl   $0x0,0x1e0(%r12)
    2aac:	e8 9f f9 ff ff       	call   2450 <pthread_create@plt>
    2ab1:	41 c7 47 04 01 00 00 00 	movl   $0x1,0x4(%r15)
    2ab9:	44 89 f2             	mov    %r14d,%edx
    2abc:	bf 01 00 00 00       	mov    $0x1,%edi
    2ac1:	31 c0                	xor    %eax,%eax
    2ac3:	41 c7 47 2c 01 00 00 00 	movl   $0x1,0x2c(%r15)
    2acb:	48 8d 35 ce 39 00 00 	lea    0x39ce(%rip),%rsi        # 64a0 <_IO_stdin_used+0x4a0>
    2ad2:	41 83 c6 01          	add    $0x1,%r14d
    2ad6:	e8 55 f9 ff ff       	call   2430 <__printf_chk@plt>
    2adb:	4c 89 f9             	mov    %r15,%rcx
    2ade:	48 89 de             	mov    %rbx,%rsi
    2ae1:	4c 89 ef             	mov    %r13,%rdi
    2ae4:	48 8d 15 65 06 00 00 	lea    0x665(%rip),%rdx        # 3150 <barriered_thread>
    2aeb:	49 83 c7 78          	add    $0x78,%r15
    2aef:	49 83 c5 08          	add    $0x8,%r13
    2af3:	48 83 c3 38          	add    $0x38,%rbx
    2af7:	e8 54 f9 ff ff       	call   2450 <pthread_create@plt>
    2afc:	41 83 fe 04          	cmp    $0x4,%r14d
    2b00:	75 af                	jne    2ab1 <main+0x551>
    2b02:	be d8 00 00 00       	mov    $0xd8,%esi
    2b07:	bf 01 00 00 00       	mov    $0x1,%edi
    2b0c:	41 c7 84 24 5c 02 00 00 02 00 00 00 	movl   $0x2,0x25c(%r12)
    2b18:	41 be 06 00 00 00    	mov    $0x6,%r14d
    2b1e:	41 c7 84 24 84 02 00 00 01 00 00 00 	movl   $0x1,0x284(%r12)
    2b2a:	4c 8d 6d 30          	lea    0x30(%rbp),%r13
    2b2e:	4d 8d bc 24 d0 02 00 00 	lea    0x2d0(%r12),%r15
    2b36:	41 c7 84 24 80 02 00 00 00 00 00 00 	movl   $0x0,0x280(%r12)
    2b42:	e8 39 f8 ff ff       	call   2380 <calloc@plt>
    2b47:	be 00 08 00 00       	mov    $0x800,%esi
    2b4c:	31 ff                	xor    %edi,%edi
    2b4e:	49 89 84 24 98 02 00 00 	mov    %rax,0x298(%r12)
    2b56:	e8 35 f9 ff ff       	call   2490 <eventfd@plt>
    2b5b:	ba 05 00 00 00       	mov    $0x5,%edx
    2b60:	bf 01 00 00 00       	mov    $0x1,%edi
    2b65:	4d 89 a4 24 68 02 00 00 	mov    %r12,0x268(%r12)
    2b6d:	41 89 84 24 a0 02 00 00 	mov    %eax,0x2a0(%r12)
    2b75:	48 8d 35 db 36 00 00 	lea    0x36db(%rip),%rsi        # 6257 <_IO_stdin_used+0x257>
    2b7c:	31 c0                	xor    %eax,%eax
    2b7e:	41 c7 84 24 70 02 00 00 04 00 00 00 	movl   $0x4,0x270(%r12)
    2b8a:	41 c7 84 24 58 02 00 00 05 00 00 00 	movl   $0x5,0x258(%r12)
    2b96:	e8 95 f8 ff ff       	call   2430 <__printf_chk@plt>
    2b9b:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    2ba0:	48 8d 7d 28          	lea    0x28(%rbp),%rdi
    2ba4:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    2ba9:	48 8d 15 e0 1a 00 00 	lea    0x1ae0(%rip),%rdx        # 4690 <io_thread>
    2bb0:	48 81 c6 18 01 00 00 	add    $0x118,%rsi
    2bb7:	e8 94 f8 ff ff       	call   2450 <pthread_create@plt>
    2bbc:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
    2bc1:	48 89 6c 24 08       	mov    %rbp,0x8(%rsp)
    2bc6:	44 89 f5             	mov    %r14d,%ebp
    2bc9:	48 81 c3 50 01 00 00 	add    $0x150,%rbx
    2bd0:	49 89 de             	mov    %rbx,%r14
    2bd3:	48 8b 5c 24 48       	mov    0x48(%rsp),%rbx
    2bd8:	89 ea                	mov    %ebp,%edx
    2bda:	48 8d 35 8d 36 00 00 	lea    0x368d(%rip),%rsi        # 626e <_IO_stdin_used+0x26e>
    2be1:	bf 01 00 00 00       	mov    $0x1,%edi
    2be6:	31 c0                	xor    %eax,%eax
    2be8:	e8 43 f8 ff ff       	call   2430 <__printf_chk@plt>
    2bed:	49 89 5f 38          	mov    %rbx,0x38(%r15)
    2bf1:	4c 89 f9             	mov    %r15,%rcx
    2bf4:	4c 89 f6             	mov    %r14,%rsi
    2bf7:	41 89 2f             	mov    %ebp,(%r15)
    2bfa:	48 8b 05 77 3c 00 00 	mov    0x3c77(%rip),%rax        # 6878 <_IO_stdin_used+0x878>
    2c01:	4c 89 ef             	mov    %r13,%rdi
    2c04:	83 c5 01             	add    $0x1,%ebp
    2c07:	4d 89 67 10          	mov    %r12,0x10(%r15)
    2c0b:	48 83 c3 10          	add    $0x10,%rbx
    2c0f:	49 83 c7 78          	add    $0x78,%r15
    2c13:	49 83 c5 08          	add    $0x8,%r13
    2c17:	49 89 47 a0          	mov    %rax,-0x60(%r15)
    2c1b:	48 8d 15 ee 06 00 00 	lea    0x6ee(%rip),%rdx        # 3310 <external_thread>
    2c22:	49 83 c6 38          	add    $0x38,%r14
    2c26:	41 c7 47 8c 03 00 00 00 	movl   $0x3,-0x74(%r15)
    2c2e:	41 c7 47 b4 01 00 00 00 	movl   $0x1,-0x4c(%r15)
    2c36:	41 c7 47 b0 00 00 00 00 	movl   $0x0,-0x50(%r15)
    2c3e:	e8 0d f8 ff ff       	call   2450 <pthread_create@plt>
    2c43:	83 fd 09             	cmp    $0x9,%ebp
    2c46:	75 90                	jne    2bd8 <main+0x678>
    2c48:	48 8d 3d 3c 36 00 00 	lea    0x363c(%rip),%rdi        # 628b <_IO_stdin_used+0x28b>
    2c4f:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    2c54:	31 db                	xor    %ebx,%ebx
    2c56:	4c 8d 74 24 50       	lea    0x50(%rsp),%r14
    2c5b:	e8 70 f6 ff ff       	call   22d0 <puts@plt>
    2c60:	4c 8d 2d 42 36 00 00 	lea    0x3642(%rip),%r13        # 62a9 <_IO_stdin_used+0x2a9>
    2c67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    2c70:	48 8b 7c dd 00       	mov    0x0(%rbp,%rbx,8),%rdi
    2c75:	4c 89 f6             	mov    %r14,%rsi
    2c78:	e8 53 f8 ff ff       	call   24d0 <pthread_join@plt>
    2c7d:	89 da                	mov    %ebx,%edx
    2c7f:	4c 89 ee             	mov    %r13,%rsi
    2c82:	bf 01 00 00 00       	mov    $0x1,%edi
    2c87:	31 c0                	xor    %eax,%eax
    2c89:	48 83 c3 01          	add    $0x1,%rbx
    2c8d:	e8 9e f7 ff ff       	call   2430 <__printf_chk@plt>
    2c92:	48 83 fb 09          	cmp    $0x9,%rbx
    2c96:	75 d8                	jne    2c70 <main+0x710>
    2c98:	49 8d 84 24 00 02 00 00 	lea    0x200(%r12),%rax
    2ca0:	45 31 f6             	xor    %r14d,%r14d
    2ca3:	31 db                	xor    %ebx,%ebx
    2ca5:	31 ed                	xor    %ebp,%ebp
    2ca7:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2cac:	4d 8d 54 24 20       	lea    0x20(%r12),%r10
    2cb1:	45 31 ff             	xor    %r15d,%r15d
    2cb4:	45 31 ed             	xor    %r13d,%r13d
    2cb7:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    2cbc:	4d 89 d4             	mov    %r10,%r12
    2cbf:	49 63 54 24 08       	movslq 0x8(%r12),%rdx
    2cc4:	85 d2                	test   %edx,%edx
    2cc6:	0f 8e 88 00 00 00    	jle    2d54 <main+0x7f4>
    2ccc:	49 8b 04 24          	mov    (%r12),%rax
    2cd0:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    2cd4:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    2cd9:	48 8d 14 4a          	lea    (%rdx,%rcx,2),%rdx
    2cdd:	48 8d 14 d0          	lea    (%rax,%rdx,8),%rdx
    2ce1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    2ce8:	48 8b 48 10          	mov    0x10(%rax),%rcx
    2cec:	48 05 98 00 00 00    	add    $0x98,%rax
    2cf2:	49 01 cd             	add    %rcx,%r13
    2cf5:	48 8b 48 80          	mov    -0x80(%rax),%rcx
    2cf9:	49 01 ce             	add    %rcx,%r14
    2cfc:	48 8b 48 d0          	mov    -0x30(%rax),%rcx
    2d00:	49 01 cf             	add    %rcx,%r15
    2d03:	48 8b 48 e0          	mov    -0x20(%rax),%rcx
    2d07:	49 01 c8             	add    %rcx,%r8
    2d0a:	48 8b 48 d8          	mov    -0x28(%rax),%rcx
    2d0e:	48 03 69 10          	add    0x10(%rcx),%rbp
    2d12:	48 8b 48 d8          	mov    -0x28(%rax),%rcx
    2d16:	48 03 59 18          	add    0x18(%rcx),%rbx
    2d1a:	48 8b 48 d8          	mov    -0x28(%rax),%rcx
    2d1e:	48 03 69 30          	add    0x30(%rcx),%rbp
    2d22:	48 8b 48 d8          	mov    -0x28(%rax),%rcx
    2d26:	48 03 59 38          	add    0x38(%rcx),%rbx
    2d2a:	48 8b 48 d8          	mov    -0x28(%rax),%rcx
    2d2e:	48 03 69 50          	add    0x50(%rcx),%rbp
    2d32:	48 8b 48 d8          	mov    -0x28(%rax),%rcx
    2d36:	48 03 59 58          	add    0x58(%rcx),%rbx
    2d3a:	48 8b 48 d8          	mov    -0x28(%rax),%rcx
    2d3e:	48 03 69 70          	add    0x70(%rcx),%rbp
    2d42:	48 8b 48 d8          	mov    -0x28(%rax),%rcx
    2d46:	48 03 59 78          	add    0x78(%rcx),%rbx
    2d4a:	48 39 d0             	cmp    %rdx,%rax
    2d4d:	75 99                	jne    2ce8 <main+0x788>
    2d4f:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    2d54:	49 8b 4c 24 48       	mov    0x48(%r12),%rcx
    2d59:	49 8b 54 24 40       	mov    0x40(%r12),%rdx
    2d5e:	31 c0                	xor    %eax,%eax
    2d60:	49 83 c4 78          	add    $0x78,%r12
    2d64:	49 2b 4c 24 c0       	sub    -0x40(%r12),%rcx
    2d69:	49 2b 54 24 b8       	sub    -0x48(%r12),%rdx
    2d6e:	bf 01 00 00 00       	mov    $0x1,%edi
    2d73:	48 8d 35 43 35 00 00 	lea    0x3543(%rip),%rsi        # 62bd <_IO_stdin_used+0x2bd>
    2d7a:	e8 b1 f6 ff ff       	call   2430 <__printf_chk@plt>
    2d7f:	49 8b 54 24 d8       	mov    -0x28(%r12),%rdx
    2d84:	48 8d 35 50 35 00 00 	lea    0x3550(%rip),%rsi        # 62db <_IO_stdin_used+0x2db>
    2d8b:	31 c0                	xor    %eax,%eax
    2d8d:	bf 01 00 00 00       	mov    $0x1,%edi
    2d92:	e8 99 f6 ff ff       	call   2430 <__printf_chk@plt>
    2d97:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    2d9c:	49 39 c4             	cmp    %rax,%r12
    2d9f:	0f 85 1a ff ff ff    	jne    2cbf <main+0x75f>
    2da5:	4c 89 ea             	mov    %r13,%rdx
    2da8:	48 8d 35 3c 35 00 00 	lea    0x353c(%rip),%rsi        # 62eb <_IO_stdin_used+0x2eb>
    2daf:	31 c0                	xor    %eax,%eax
    2db1:	4d 89 f4             	mov    %r14,%r12
    2db4:	bf 01 00 00 00       	mov    $0x1,%edi
    2db9:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    2dbe:	e8 6d f6 ff ff       	call   2430 <__printf_chk@plt>
    2dc3:	bf 0a 00 00 00       	mov    $0xa,%edi
    2dc8:	e8 f3 f4 ff ff       	call   22c0 <putchar@plt>
    2dcd:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    2dd2:	bf 01 00 00 00       	mov    $0x1,%edi
    2dd7:	48 8d 35 21 35 00 00 	lea    0x3521(%rip),%rsi        # 62ff <_IO_stdin_used+0x2ff>
    2dde:	48 8b 10             	mov    (%rax),%rdx
    2de1:	31 c0                	xor    %eax,%eax
    2de3:	e8 48 f6 ff ff       	call   2430 <__printf_chk@plt>
    2de8:	4c 89 e2             	mov    %r12,%rdx
    2deb:	bf 01 00 00 00       	mov    $0x1,%edi
    2df0:	31 c0                	xor    %eax,%eax
    2df2:	48 8d 35 1b 35 00 00 	lea    0x351b(%rip),%rsi        # 6314 <_IO_stdin_used+0x314>
    2df9:	49 bc 89 88 88 88 88 88 88 88 	movabs $0x8888888888888889,%r12
    2e03:	e8 28 f6 ff ff       	call   2430 <__printf_chk@plt>
    2e08:	bf 0a 00 00 00       	mov    $0xa,%edi
    2e0d:	e8 ae f4 ff ff       	call   22c0 <putchar@plt>
    2e12:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    2e17:	bf 01 00 00 00       	mov    $0x1,%edi
    2e1c:	48 8d 35 a5 36 00 00 	lea    0x36a5(%rip),%rsi        # 64c8 <_IO_stdin_used+0x4c8>
    2e23:	48 8b 08             	mov    (%rax),%rcx
    2e26:	48 89 c8             	mov    %rcx,%rax
    2e29:	49 f7 ec             	imul   %r12
    2e2c:	31 c0                	xor    %eax,%eax
    2e2e:	48 01 ca             	add    %rcx,%rdx
    2e31:	48 c1 f9 3f          	sar    $0x3f,%rcx
    2e35:	48 c1 fa 04          	sar    $0x4,%rdx
    2e39:	48 29 ca             	sub    %rcx,%rdx
    2e3c:	e8 ef f5 ff ff       	call   2430 <__printf_chk@plt>
    2e41:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    2e46:	bf 01 00 00 00       	mov    $0x1,%edi
    2e4b:	48 8d 35 96 36 00 00 	lea    0x3696(%rip),%rsi        # 64e8 <_IO_stdin_used+0x4e8>
    2e52:	48 8b 50 08          	mov    0x8(%rax),%rdx
    2e56:	31 c0                	xor    %eax,%eax
    2e58:	e8 d3 f5 ff ff       	call   2430 <__printf_chk@plt>
    2e5d:	4c 89 f8             	mov    %r15,%rax
    2e60:	4d 89 f9             	mov    %r15,%r9
    2e63:	bf 01 00 00 00       	mov    $0x1,%edi
    2e68:	49 f7 ec             	imul   %r12
    2e6b:	49 c1 f9 3f          	sar    $0x3f,%r9
    2e6f:	48 8d 35 9a 36 00 00 	lea    0x369a(%rip),%rsi        # 6510 <_IO_stdin_used+0x510>
    2e76:	31 c0                	xor    %eax,%eax
    2e78:	4c 01 fa             	add    %r15,%rdx
    2e7b:	48 c1 fa 04          	sar    $0x4,%rdx
    2e7f:	4c 29 ca             	sub    %r9,%rdx
    2e82:	e8 a9 f5 ff ff       	call   2430 <__printf_chk@plt>
    2e87:	4c 89 f0             	mov    %r14,%rax
    2e8a:	4d 89 f0             	mov    %r14,%r8
    2e8d:	bf 01 00 00 00       	mov    $0x1,%edi
    2e92:	49 f7 ec             	imul   %r12
    2e95:	49 c1 f8 3f          	sar    $0x3f,%r8
    2e99:	48 8d 35 a0 36 00 00 	lea    0x36a0(%rip),%rsi        # 6540 <_IO_stdin_used+0x540>
    2ea0:	31 c0                	xor    %eax,%eax
    2ea2:	4c 01 f2             	add    %r14,%rdx
    2ea5:	48 c1 fa 04          	sar    $0x4,%rdx
    2ea9:	4c 29 c2             	sub    %r8,%rdx
    2eac:	e8 7f f5 ff ff       	call   2430 <__printf_chk@plt>
    2eb1:	4c 89 e8             	mov    %r13,%rax
    2eb4:	bf 01 00 00 00       	mov    $0x1,%edi
    2eb9:	48 8d 35 b0 36 00 00 	lea    0x36b0(%rip),%rsi        # 6570 <_IO_stdin_used+0x570>
    2ec0:	49 f7 ec             	imul   %r12
    2ec3:	4c 01 ea             	add    %r13,%rdx
    2ec6:	49 c1 fd 3f          	sar    $0x3f,%r13
    2eca:	31 c0                	xor    %eax,%eax
    2ecc:	48 c1 fa 04          	sar    $0x4,%rdx
    2ed0:	4c 29 ea             	sub    %r13,%rdx
    2ed3:	e8 58 f5 ff ff       	call   2430 <__printf_chk@plt>
    2ed8:	48 89 e8             	mov    %rbp,%rax
    2edb:	bf 01 00 00 00       	mov    $0x1,%edi
    2ee0:	48 8d 35 3a 34 00 00 	lea    0x343a(%rip),%rsi        # 6321 <_IO_stdin_used+0x321>
    2ee7:	49 f7 ec             	imul   %r12
    2eea:	31 c0                	xor    %eax,%eax
    2eec:	48 01 ea             	add    %rbp,%rdx
    2eef:	48 c1 fd 3f          	sar    $0x3f,%rbp
    2ef3:	48 c1 fa 04          	sar    $0x4,%rdx
    2ef7:	48 29 ea             	sub    %rbp,%rdx
    2efa:	e8 31 f5 ff ff       	call   2430 <__printf_chk@plt>
    2eff:	48 89 d8             	mov    %rbx,%rax
    2f02:	bf 01 00 00 00       	mov    $0x1,%edi
    2f07:	48 8d 35 24 34 00 00 	lea    0x3424(%rip),%rsi        # 6332 <_IO_stdin_used+0x332>
    2f0e:	49 f7 ec             	imul   %r12
    2f11:	31 c0                	xor    %eax,%eax
    2f13:	48 01 da             	add    %rbx,%rdx
    2f16:	48 c1 fb 3f          	sar    $0x3f,%rbx
    2f1a:	48 c1 fa 04          	sar    $0x4,%rdx
    2f1e:	48 29 da             	sub    %rbx,%rdx
    2f21:	e8 0a f5 ff ff       	call   2430 <__printf_chk@plt>
    2f26:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    2f2b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    2f34:	75 67                	jne    2f9d <main+0xa3d>
    2f36:	48 83 c4 68          	add    $0x68,%rsp
    2f3a:	31 c0                	xor    %eax,%eax
    2f3c:	5b                   	pop    %rbx
    2f3d:	5d                   	pop    %rbp
    2f3e:	41 5c                	pop    %r12
    2f40:	41 5d                	pop    %r13
    2f42:	41 5e                	pop    %r14
    2f44:	41 5f                	pop    %r15
    2f46:	c3                   	ret
    2f47:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    2f50:	8b 54 24 20          	mov    0x20(%rsp),%edx
    2f54:	bf 01 00 00 00       	mov    $0x1,%edi
    2f59:	48 8d 35 e5 32 00 00 	lea    0x32e5(%rip),%rsi        # 6245 <_IO_stdin_used+0x245>
    2f60:	31 c0                	xor    %eax,%eax
    2f62:	e8 c9 f4 ff ff       	call   2430 <__printf_chk@plt>
    2f67:	48 63 44 24 28       	movslq 0x28(%rsp),%rax
    2f6c:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
    2f71:	48 89 c7             	mov    %rax,%rdi
    2f74:	48 c1 e0 04          	shl    $0x4,%rax
    2f78:	48 01 d0             	add    %rdx,%rax
    2f7b:	49 8b 57 20          	mov    0x20(%r15),%rdx
    2f7f:	49 89 47 38          	mov    %rax,0x38(%r15)
    2f83:	48 8d 05 b6 21 00 00 	lea    0x21b6(%rip),%rax        # 5140 <barriered_work_ingest>
    2f8a:	48 01 d5             	add    %rdx,%rbp
    2f8d:	48 89 45 20          	mov    %rax,0x20(%rbp)
    2f91:	8d 47 01             	lea    0x1(%rdi),%eax
    2f94:	89 44 24 28          	mov    %eax,0x28(%rsp)
    2f98:	e9 33 f9 ff ff       	jmp    28d0 <main+0x370>
    2f9d:	e8 6e f3 ff ff       	call   2310 <__stack_chk_fail@plt>
    2fa2:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    2fac:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000002fb0 <_start>:
    2fb0:	f3 0f 1e fa          	endbr64
    2fb4:	31 ed                	xor    %ebp,%ebp
    2fb6:	49 89 d1             	mov    %rdx,%r9
    2fb9:	5e                   	pop    %rsi
    2fba:	48 89 e2             	mov    %rsp,%rdx
    2fbd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    2fc1:	50                   	push   %rax
    2fc2:	54                   	push   %rsp
    2fc3:	45 31 c0             	xor    %r8d,%r8d
    2fc6:	31 c9                	xor    %ecx,%ecx
    2fc8:	48 8d 3d 91 f5 ff ff 	lea    -0xa6f(%rip),%rdi        # 2560 <main>
    2fcf:	ff 15 03 60 00 00    	call   *0x6003(%rip)        # 8fd8 <__libc_start_main@GLIBC_2.34>
    2fd5:	f4                   	hlt
    2fd6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000002fe0 <deregister_tm_clones>:
    2fe0:	48 8d 3d 39 60 00 00 	lea    0x6039(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    2fe7:	48 8d 05 32 60 00 00 	lea    0x6032(%rip),%rax        # 9020 <stderr@GLIBC_2.2.5>
    2fee:	48 39 f8             	cmp    %rdi,%rax
    2ff1:	74 15                	je     3008 <deregister_tm_clones+0x28>
    2ff3:	48 8b 05 e6 5f 00 00 	mov    0x5fe6(%rip),%rax        # 8fe0 <_ITM_deregisterTMCloneTable@Base>
    2ffa:	48 85 c0             	test   %rax,%rax
    2ffd:	74 09                	je     3008 <deregister_tm_clones+0x28>
    2fff:	ff e0                	jmp    *%rax
    3001:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3008:	c3                   	ret
    3009:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003010 <register_tm_clones>:
    3010:	48 8d 3d 09 60 00 00 	lea    0x6009(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    3017:	48 8d 35 02 60 00 00 	lea    0x6002(%rip),%rsi        # 9020 <stderr@GLIBC_2.2.5>
    301e:	48 29 fe             	sub    %rdi,%rsi
    3021:	48 89 f0             	mov    %rsi,%rax
    3024:	48 c1 ee 3f          	shr    $0x3f,%rsi
    3028:	48 c1 f8 03          	sar    $0x3,%rax
    302c:	48 01 c6             	add    %rax,%rsi
    302f:	48 d1 fe             	sar    %rsi
    3032:	74 14                	je     3048 <register_tm_clones+0x38>
    3034:	48 8b 05 b5 5f 00 00 	mov    0x5fb5(%rip),%rax        # 8ff0 <_ITM_registerTMCloneTable@Base>
    303b:	48 85 c0             	test   %rax,%rax
    303e:	74 08                	je     3048 <register_tm_clones+0x38>
    3040:	ff e0                	jmp    *%rax
    3042:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3048:	c3                   	ret
    3049:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003050 <__do_global_dtors_aux>:
    3050:	f3 0f 1e fa          	endbr64
    3054:	80 3d cd 5f 00 00 00 	cmpb   $0x0,0x5fcd(%rip)        # 9028 <completed.0>
    305b:	75 2b                	jne    3088 <__do_global_dtors_aux+0x38>
    305d:	55                   	push   %rbp
    305e:	48 83 3d 92 5f 00 00 00 	cmpq   $0x0,0x5f92(%rip)        # 8ff8 <__cxa_finalize@GLIBC_2.2.5>
    3066:	48 89 e5             	mov    %rsp,%rbp
    3069:	74 0c                	je     3077 <__do_global_dtors_aux+0x27>
    306b:	48 8b 3d 96 5f 00 00 	mov    0x5f96(%rip),%rdi        # 9008 <__dso_handle>
    3072:	e8 29 f2 ff ff       	call   22a0 <__cxa_finalize@plt>
    3077:	e8 64 ff ff ff       	call   2fe0 <deregister_tm_clones>
    307c:	c6 05 a5 5f 00 00 01 	movb   $0x1,0x5fa5(%rip)        # 9028 <completed.0>
    3083:	5d                   	pop    %rbp
    3084:	c3                   	ret
    3085:	0f 1f 00             	nopl   (%rax)
    3088:	c3                   	ret
    3089:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003090 <frame_dummy>:
    3090:	f3 0f 1e fa          	endbr64
    3094:	e9 77 ff ff ff       	jmp    3010 <register_tm_clones>
    3099:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000030a0 <do_protected_write>:
    30a0:	f3 0f 1e fa          	endbr64
    30a4:	48 8b 47 30          	mov    0x30(%rdi),%rax
    30a8:	48 8b 57 18          	mov    0x18(%rdi),%rdx
    30ac:	48 8b 40 30          	mov    0x30(%rax),%rax
    30b0:	48 83 c2 01          	add    $0x1,%rdx
    30b4:	48 89 57 18          	mov    %rdx,0x18(%rdi)
    30b8:	48 8b 48 08          	mov    0x8(%rax),%rcx
    30bc:	48 83 00 01          	addq   $0x1,(%rax)
    30c0:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    30c7:	48 85 c9             	test   %rcx,%rcx
    30ca:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    30d1:	48 0f 4f d6          	cmovg  %rsi,%rdx
    30d5:	48 89 50 08          	mov    %rdx,0x8(%rax)
    30d9:	31 c0                	xor    %eax,%eax
    30db:	c3                   	ret
    30dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000030e0 <barriered_reset>:
    30e0:	f3 0f 1e fa          	endbr64
    30e4:	8b 47 44             	mov    0x44(%rdi),%eax
    30e7:	48 89 f9             	mov    %rdi,%rcx
    30ea:	85 c0                	test   %eax,%eax
    30ec:	7e 57                	jle    3145 <barriered_reset+0x65>
    30ee:	31 f6                	xor    %esi,%esi
    30f0:	31 ff                	xor    %edi,%edi
    30f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    30f8:	4c 8b 41 30          	mov    0x30(%rcx),%r8
    30fc:	48 63 51 38          	movslq 0x38(%rcx),%rdx
    3100:	83 c7 01             	add    $0x1,%edi
    3103:	48 89 d0             	mov    %rdx,%rax
    3106:	48 c1 e0 04          	shl    $0x4,%rax
    310a:	48 29 d0             	sub    %rdx,%rax
    310d:	49 8b 50 10          	mov    0x10(%r8),%rdx
    3111:	48 8d 04 c2          	lea    (%rdx,%rax,8),%rax
    3115:	48 8b 50 20          	mov    0x20(%rax),%rdx
    3119:	48 01 f2             	add    %rsi,%rdx
    311c:	8b 42 08             	mov    0x8(%rdx),%eax
    311f:	83 c0 01             	add    $0x1,%eax
    3122:	89 42 08             	mov    %eax,0x8(%rdx)
    3125:	48 8b 41 30          	mov    0x30(%rcx),%rax
    3129:	48 8b 50 20          	mov    0x20(%rax),%rdx
    312d:	48 01 f2             	add    %rsi,%rdx
    3130:	48 81 c6 98 00 00 00 	add    $0x98,%rsi
    3137:	c7 42 40 01 00 00 00 	movl   $0x1,0x40(%rdx)
    313e:	8b 41 44             	mov    0x44(%rcx),%eax
    3141:	39 f8                	cmp    %edi,%eax
    3143:	7f b3                	jg     30f8 <barriered_reset+0x18>
    3145:	0f ae f0             	mfence
    3148:	31 c0                	xor    %eax,%eax
    314a:	c3                   	ret
    314b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003150 <barriered_thread>:
    3150:	f3 0f 1e fa          	endbr64
    3154:	8b 47 2c             	mov    0x2c(%rdi),%eax
    3157:	83 f8 01             	cmp    $0x1,%eax
    315a:	0f 85 9f 01 00 00    	jne    32ff <barriered_thread+0x1af>
    3160:	41 55                	push   %r13
    3162:	49 89 fd             	mov    %rdi,%r13
    3165:	41 54                	push   %r12
    3167:	4c 8d 67 60          	lea    0x60(%rdi),%r12
    316b:	55                   	push   %rbp
    316c:	53                   	push   %rbx
    316d:	31 db                	xor    %ebx,%ebx
    316f:	48 83 ec 08          	sub    $0x8,%rsp
    3173:	44 8b 57 28          	mov    0x28(%rdi),%r10d
    3177:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3180:	44 39 d3             	cmp    %r10d,%ebx
    3183:	7c 0b                	jl     3190 <barriered_thread+0x40>
    3185:	31 db                	xor    %ebx,%ebx
    3187:	45 85 d2             	test   %r10d,%r10d
    318a:	0f 8e 20 01 00 00    	jle    32b0 <barriered_thread+0x160>
    3190:	48 63 c3             	movslq %ebx,%rax
    3193:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3197:	48 8d 2c 50          	lea    (%rax,%rdx,2),%rbp
    319b:	48 c1 e5 03          	shl    $0x3,%rbp
    319f:	eb 1a                	jmp    31bb <barriered_thread+0x6b>
    31a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    31a8:	83 c3 01             	add    $0x1,%ebx
    31ab:	48 81 c5 98 00 00 00 	add    $0x98,%rbp
    31b2:	44 39 d3             	cmp    %r10d,%ebx
    31b5:	0f 8d f5 00 00 00    	jge    32b0 <barriered_thread+0x160>
    31bb:	49 8b 55 20          	mov    0x20(%r13),%rdx
    31bf:	48 01 ea             	add    %rbp,%rdx
    31c2:	8b 42 40             	mov    0x40(%rdx),%eax
    31c5:	83 f8 01             	cmp    $0x1,%eax
    31c8:	75 de                	jne    31a8 <barriered_thread+0x58>
    31ca:	85 db                	test   %ebx,%ebx
    31cc:	0f 8e fe 00 00 00    	jle    32d0 <barriered_thread+0x180>
    31d2:	45 8b 5d 18          	mov    0x18(%r13),%r11d
    31d6:	8d 43 ff             	lea    -0x1(%rbx),%eax
    31d9:	45 85 db             	test   %r11d,%r11d
    31dc:	7e 6e                	jle    324c <barriered_thread+0xfc>
    31de:	48 98                	cltq
    31e0:	49 63 f3             	movslq %r11d,%rsi
    31e3:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
    31e7:	4c 8d 04 48          	lea    (%rax,%rcx,2),%r8
    31eb:	48 89 f1             	mov    %rsi,%rcx
    31ee:	49 8b 45 10          	mov    0x10(%r13),%rax
    31f2:	48 c1 e1 04          	shl    $0x4,%rcx
    31f6:	49 c1 e0 03          	shl    $0x3,%r8
    31fa:	48 29 f1             	sub    %rsi,%rcx
    31fd:	4c 8d 0c c8          	lea    (%rax,%rcx,8),%r9
    3201:	31 c9                	xor    %ecx,%ecx
    3203:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3208:	48 8b 70 20          	mov    0x20(%rax),%rsi
    320c:	4c 01 c6             	add    %r8,%rsi
    320f:	8b 76 08             	mov    0x8(%rsi),%esi
    3212:	8b 7a 08             	mov    0x8(%rdx),%edi
    3215:	39 f7                	cmp    %esi,%edi
    3217:	40 0f 94 c6          	sete   %sil
    321b:	48 83 c0 78          	add    $0x78,%rax
    321f:	40 0f b6 f6          	movzbl %sil,%esi
    3223:	01 f1                	add    %esi,%ecx
    3225:	4c 39 c8             	cmp    %r9,%rax
    3228:	75 de                	jne    3208 <barriered_thread+0xb8>
    322a:	44 39 d9             	cmp    %r11d,%ecx
    322d:	74 04                	je     3233 <barriered_thread+0xe3>
    322f:	85 c9                	test   %ecx,%ecx
    3231:	75 7d                	jne    32b0 <barriered_thread+0x160>
    3233:	85 db                	test   %ebx,%ebx
    3235:	75 15                	jne    324c <barriered_thread+0xfc>
    3237:	49 8d 75 50          	lea    0x50(%r13),%rsi
    323b:	bf 04 00 00 00       	mov    $0x4,%edi
    3240:	e8 ab f0 ff ff       	call   22f0 <clock_gettime@plt>
    3245:	49 8b 55 20          	mov    0x20(%r13),%rdx
    3249:	48 01 ea             	add    %rbp,%rdx
    324c:	c7 42 40 00 00 00 00 	movl   $0x0,0x40(%rdx)
    3253:	48 8b 4a 20          	mov    0x20(%rdx),%rcx
    3257:	49 63 55 00          	movslq 0x0(%r13),%rdx
    325b:	48 89 d0             	mov    %rdx,%rax
    325e:	48 c1 e0 04          	shl    $0x4,%rax
    3262:	48 29 d0             	sub    %rdx,%rax
    3265:	49 8b 55 10          	mov    0x10(%r13),%rdx
    3269:	48 8d 04 c2          	lea    (%rdx,%rax,8),%rax
    326d:	48 8b 78 20          	mov    0x20(%rax),%rdi
    3271:	48 01 ef             	add    %rbp,%rdi
    3274:	ff d1                	call   *%rcx
    3276:	49 8b 55 20          	mov    0x20(%r13),%rdx
    327a:	48 01 ea             	add    %rbp,%rdx
    327d:	8b 42 08             	mov    0x8(%rdx),%eax
    3280:	83 c0 01             	add    $0x1,%eax
    3283:	89 42 08             	mov    %eax,0x8(%rdx)
    3286:	41 8b 45 28          	mov    0x28(%r13),%eax
    328a:	49 83 45 70 01       	addq   $0x1,0x70(%r13)
    328f:	83 e8 01             	sub    $0x1,%eax
    3292:	39 d8                	cmp    %ebx,%eax
    3294:	74 5a                	je     32f0 <barriered_thread+0x1a0>
    3296:	0f ae f0             	mfence
    3299:	45 8b 55 28          	mov    0x28(%r13),%r10d
    329d:	83 c3 01             	add    $0x1,%ebx
    32a0:	48 81 c5 98 00 00 00 	add    $0x98,%rbp
    32a7:	44 39 d3             	cmp    %r10d,%ebx
    32aa:	0f 8c 0b ff ff ff    	jl     31bb <barriered_thread+0x6b>
    32b0:	41 8b 45 2c          	mov    0x2c(%r13),%eax
    32b4:	83 f8 01             	cmp    $0x1,%eax
    32b7:	0f 84 c3 fe ff ff    	je     3180 <barriered_thread+0x30>
    32bd:	48 83 c4 08          	add    $0x8,%rsp
    32c1:	31 c0                	xor    %eax,%eax
    32c3:	5b                   	pop    %rbx
    32c4:	5d                   	pop    %rbp
    32c5:	41 5c                	pop    %r12
    32c7:	41 5d                	pop    %r13
    32c9:	c3                   	ret
    32ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    32d0:	45 8b 5d 18          	mov    0x18(%r13),%r11d
    32d4:	41 8d 42 ff          	lea    -0x1(%r10),%eax
    32d8:	45 85 db             	test   %r11d,%r11d
    32db:	0f 8f fd fe ff ff    	jg     31de <barriered_thread+0x8e>
    32e1:	e9 4d ff ff ff       	jmp    3233 <barriered_thread+0xe3>
    32e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    32f0:	4c 89 e6             	mov    %r12,%rsi
    32f3:	bf 04 00 00 00       	mov    $0x4,%edi
    32f8:	e8 f3 ef ff ff       	call   22f0 <clock_gettime@plt>
    32fd:	eb 97                	jmp    3296 <barriered_thread+0x146>
    32ff:	31 c0                	xor    %eax,%eax
    3301:	c3                   	ret
    3302:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    330d:	0f 1f 00             	nopl   (%rax)

0000000000003310 <external_thread>:
    3310:	f3 0f 1e fa          	endbr64
    3314:	41 55                	push   %r13
    3316:	41 54                	push   %r12
    3318:	55                   	push   %rbp
    3319:	53                   	push   %rbx
    331a:	48 83 ec 38          	sub    $0x38,%rsp
    331e:	66 0f 6f 05 6a 34 00 00 	movdqa 0x346a(%rip),%xmm0        # 6790 <_IO_stdin_used+0x790>
    3326:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    332f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    3334:	31 c0                	xor    %eax,%eax
    3336:	0f 29 04 24          	movaps %xmm0,(%rsp)
    333a:	8b 47 2c             	mov    0x2c(%rdi),%eax
    333d:	83 f8 01             	cmp    $0x1,%eax
    3340:	75 64                	jne    33a6 <external_thread+0x96>
    3342:	49 89 fd             	mov    %rdi,%r13
    3345:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    334a:	48 89 e3             	mov    %rsp,%rbx
    334d:	4c 8d 25 b0 2c 00 00 	lea    0x2cb0(%rip),%r12        # 6004 <_IO_stdin_used+0x4>
    3354:	0f 1f 40 00          	nopl   0x0(%rax)
    3358:	48 89 ee             	mov    %rbp,%rsi
    335b:	48 89 df             	mov    %rbx,%rdi
    335e:	e8 cd ef ff ff       	call   2330 <nanosleep@plt>
    3363:	49 8b 45 38          	mov    0x38(%r13),%rax
    3367:	48 63 08             	movslq (%rax),%rcx
    336a:	85 c9                	test   %ecx,%ecx
    336c:	7e 2c                	jle    339a <external_thread+0x8a>
    336e:	48 8b 40 08          	mov    0x8(%rax),%rax
    3372:	48 c1 e1 04          	shl    $0x4,%rcx
    3376:	48 01 c1             	add    %rax,%rcx
    3379:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3380:	8b 50 08             	mov    0x8(%rax),%edx
    3383:	85 d2                	test   %edx,%edx
    3385:	75 0a                	jne    3391 <external_thread+0x81>
    3387:	4c 89 20             	mov    %r12,(%rax)
    338a:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    3391:	48 83 c0 10          	add    $0x10,%rax
    3395:	48 39 c1             	cmp    %rax,%rcx
    3398:	75 e6                	jne    3380 <external_thread+0x70>
    339a:	0f ae f0             	mfence
    339d:	41 8b 45 2c          	mov    0x2c(%r13),%eax
    33a1:	83 f8 01             	cmp    $0x1,%eax
    33a4:	74 b2                	je     3358 <external_thread+0x48>
    33a6:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    33ab:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    33b4:	75 0d                	jne    33c3 <external_thread+0xb3>
    33b6:	48 83 c4 38          	add    $0x38,%rsp
    33ba:	31 c0                	xor    %eax,%eax
    33bc:	5b                   	pop    %rbx
    33bd:	5d                   	pop    %rbp
    33be:	41 5c                	pop    %r12
    33c0:	41 5d                	pop    %r13
    33c2:	c3                   	ret
    33c3:	e8 48 ef ff ff       	call   2310 <__stack_chk_fail@plt>
    33c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

00000000000033d0 <timer_thread>:
    33d0:	f3 0f 1e fa          	endbr64
    33d4:	41 57                	push   %r15
    33d6:	48 8d 35 33 2c 00 00 	lea    0x2c33(%rip),%rsi        # 6010 <_IO_stdin_used+0x10>
    33dd:	49 89 ff             	mov    %rdi,%r15
    33e0:	41 56                	push   %r14
    33e2:	41 55                	push   %r13
    33e4:	41 54                	push   %r12
    33e6:	55                   	push   %rbp
    33e7:	53                   	push   %rbx
    33e8:	48 83 ec 58          	sub    $0x58,%rsp
    33ec:	8b 17                	mov    (%rdi),%edx
    33ee:	bf 01 00 00 00       	mov    $0x1,%edi
    33f3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    33fc:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3401:	31 c0                	xor    %eax,%eax
    3403:	e8 28 f0 ff ff       	call   2430 <__printf_chk@plt>
    3408:	66 0f 6f 05 80 33 00 00 	movdqa 0x3380(%rip),%xmm0        # 6790 <_IO_stdin_used+0x790>
    3410:	ba 30 75 00 00       	mov    $0x7530,%edx
    3415:	31 c0                	xor    %eax,%eax
    3417:	48 8d 35 04 2c 00 00 	lea    0x2c04(%rip),%rsi        # 6022 <_IO_stdin_used+0x22>
    341e:	bf 01 00 00 00       	mov    $0x1,%edi
    3423:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    3428:	e8 03 f0 ff ff       	call   2430 <__printf_chk@plt>
    342d:	4d 63 77 2c          	movslq 0x2c(%r15),%r14
    3431:	45 85 f6             	test   %r14d,%r14d
    3434:	0f 84 a6 00 00 00    	je     34e0 <timer_thread+0x110>
    343a:	45 31 ed             	xor    %r13d,%r13d
    343d:	45 31 f6             	xor    %r14d,%r14d
    3440:	49 89 e4             	mov    %rsp,%r12
    3443:	31 db                	xor    %ebx,%ebx
    3445:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    344a:	48 89 ef             	mov    %rbp,%rdi
    344d:	4c 89 e6             	mov    %r12,%rsi
    3450:	41 83 c5 01          	add    $0x1,%r13d
    3454:	e8 d7 ee ff ff       	call   2330 <nanosleep@plt>
    3459:	49 63 47 18          	movslq 0x18(%r15),%rax
    345d:	41 8d 7e 01          	lea    0x1(%r14),%edi
    3461:	85 c0                	test   %eax,%eax
    3463:	7e 56                	jle    34bb <timer_thread+0xeb>
    3465:	4b 8d 14 f6          	lea    (%r14,%r14,8),%rdx
    3469:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    346d:	4d 8d 04 56          	lea    (%r14,%rdx,2),%r8
    3471:	48 89 c2             	mov    %rax,%rdx
    3474:	48 c1 e2 04          	shl    $0x4,%rdx
    3478:	49 c1 e0 03          	shl    $0x3,%r8
    347c:	48 29 c2             	sub    %rax,%rdx
    347f:	4c 8d 0c d1          	lea    (%rcx,%rdx,8),%r9
    3483:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3488:	89 f8                	mov    %edi,%eax
    348a:	48 8b 71 20          	mov    0x20(%rcx),%rsi
    348e:	99                   	cltd
    348f:	f7 79 28             	idivl  0x28(%rcx)
    3492:	48 83 c1 78          	add    $0x78,%rcx
    3496:	48 63 d2             	movslq %edx,%rdx
    3499:	48 8d 04 d2          	lea    (%rdx,%rdx,8),%rax
    349d:	48 8d 04 42          	lea    (%rdx,%rax,2),%rax
    34a1:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
    34a5:	4c 01 c6             	add    %r8,%rsi
    34a8:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    34af:	c7 46 48 00 00 00 00 	movl   $0x0,0x48(%rsi)
    34b6:	4c 39 c9             	cmp    %r9,%rcx
    34b9:	75 cd                	jne    3488 <timer_thread+0xb8>
    34bb:	0f ae f0             	mfence
    34be:	49 8b 47 10          	mov    0x10(%r15),%rax
    34c2:	39 78 28             	cmp    %edi,0x28(%rax)
    34c5:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    34c9:	0f 4e fb             	cmovle %ebx,%edi
    34cc:	4c 63 f7             	movslq %edi,%r14
    34cf:	85 c0                	test   %eax,%eax
    34d1:	74 0d                	je     34e0 <timer_thread+0x110>
    34d3:	41 81 fd 30 75 00 00 	cmp    $0x7530,%r13d
    34da:	0f 85 6a ff ff ff    	jne    344a <timer_thread+0x7a>
    34e0:	48 8d 3d 51 2b 00 00 	lea    0x2b51(%rip),%rdi        # 6038 <_IO_stdin_used+0x38>
    34e7:	e8 e4 ed ff ff       	call   22d0 <puts@plt>
    34ec:	49 63 57 1c          	movslq 0x1c(%r15),%rdx
    34f0:	85 d2                	test   %edx,%edx
    34f2:	7e 52                	jle    3546 <timer_thread+0x176>
    34f4:	49 63 47 28          	movslq 0x28(%r15),%rax
    34f8:	85 c0                	test   %eax,%eax
    34fa:	7e 4a                	jle    3546 <timer_thread+0x176>
    34fc:	48 89 d1             	mov    %rdx,%rcx
    34ff:	4d 8b 47 10          	mov    0x10(%r15),%r8
    3503:	31 f6                	xor    %esi,%esi
    3505:	48 c1 e1 04          	shl    $0x4,%rcx
    3509:	48 29 d1             	sub    %rdx,%rcx
    350c:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    3510:	48 8d 3c 50          	lea    (%rax,%rdx,2),%rdi
    3514:	48 c1 e1 03          	shl    $0x3,%rcx
    3518:	48 c1 e7 03          	shl    $0x3,%rdi
    351c:	49 8b 44 30 20       	mov    0x20(%r8,%rsi,1),%rax
    3521:	48 8d 14 07          	lea    (%rdi,%rax,1),%rdx
    3525:	0f 1f 00             	nopl   (%rax)
    3528:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
    3532:	48 05 98 00 00 00    	add    $0x98,%rax
    3538:	48 39 d0             	cmp    %rdx,%rax
    353b:	75 eb                	jne    3528 <timer_thread+0x158>
    353d:	48 83 c6 78          	add    $0x78,%rsi
    3541:	48 39 ce             	cmp    %rcx,%rsi
    3544:	75 d6                	jne    351c <timer_thread+0x14c>
    3546:	0f ae f0             	mfence
    3549:	66 0f 6f 05 4f 32 00 00 	movdqa 0x324f(%rip),%xmm0        # 67a0 <_IO_stdin_used+0x7a0>
    3551:	48 8d 2d 05 2b 00 00 	lea    0x2b05(%rip),%rbp        # 605d <_IO_stdin_used+0x5d>
    3558:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    355d:	49 63 47 18          	movslq 0x18(%r15),%rax
    3561:	45 8d 6e 01          	lea    0x1(%r14),%r13d
    3565:	85 c0                	test   %eax,%eax
    3567:	7e 5b                	jle    35c4 <timer_thread+0x1f4>
    3569:	4b 8d 14 f6          	lea    (%r14,%r14,8),%rdx
    356d:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    3571:	49 8d 3c 56          	lea    (%r14,%rdx,2),%rdi
    3575:	48 89 c2             	mov    %rax,%rdx
    3578:	48 c1 e2 04          	shl    $0x4,%rdx
    357c:	48 c1 e7 03          	shl    $0x3,%rdi
    3580:	48 29 c2             	sub    %rax,%rdx
    3583:	4c 8d 04 d1          	lea    (%rcx,%rdx,8),%r8
    3587:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3590:	44 89 e8             	mov    %r13d,%eax
    3593:	48 8b 71 20          	mov    0x20(%rcx),%rsi
    3597:	99                   	cltd
    3598:	f7 79 28             	idivl  0x28(%rcx)
    359b:	48 83 c1 78          	add    $0x78,%rcx
    359f:	48 63 c2             	movslq %edx,%rax
    35a2:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    35a6:	48 8d 04 50          	lea    (%rax,%rdx,2),%rax
    35aa:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
    35ae:	48 01 fe             	add    %rdi,%rsi
    35b1:	c7 40 48 01 00 00 00 	movl   $0x1,0x48(%rax)
    35b8:	c7 46 48 00 00 00 00 	movl   $0x0,0x48(%rsi)
    35bf:	49 39 c8             	cmp    %rcx,%r8
    35c2:	75 cc                	jne    3590 <timer_thread+0x1c0>
    35c4:	0f ae f0             	mfence
    35c7:	49 8b 47 10          	mov    0x10(%r15),%rax
    35cb:	44 39 68 28          	cmp    %r13d,0x28(%rax)
    35cf:	7f 03                	jg     35d4 <timer_thread+0x204>
    35d1:	45 31 ed             	xor    %r13d,%r13d
    35d4:	45 8b 47 18          	mov    0x18(%r15),%r8d
    35d8:	45 85 c0             	test   %r8d,%r8d
    35db:	0f 8e dd 00 00 00    	jle    36be <timer_thread+0x2ee>
    35e1:	31 db                	xor    %ebx,%ebx
    35e3:	45 31 e4             	xor    %r12d,%r12d
    35e6:	41 b9 01 00 00 00    	mov    $0x1,%r9d
    35ec:	0f 1f 40 00          	nopl   0x0(%rax)
    35f0:	45 31 f6             	xor    %r14d,%r14d
    35f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    35f8:	45 85 c0             	test   %r8d,%r8d
    35fb:	0f 8e 81 00 00 00    	jle    3682 <timer_thread+0x2b2>
    3601:	49 8b 47 10          	mov    0x10(%r15),%rax
    3605:	4b 8d 14 f6          	lea    (%r14,%r14,8),%rdx
    3609:	49 63 f8             	movslq %r8d,%rdi
    360c:	49 8d 14 56          	lea    (%r14,%rdx,2),%rdx
    3610:	48 8b 44 18 20       	mov    0x20(%rax,%rbx,1),%rax
    3615:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    3619:	31 d2                	xor    %edx,%edx
    361b:	eb 1e                	jmp    363b <timer_thread+0x26b>
    361d:	0f 1f 00             	nopl   (%rax)
    3620:	48 8b 71 70          	mov    0x70(%rcx),%rsi
    3624:	48 8b 74 06 08       	mov    0x8(%rsi,%rax,1),%rsi
    3629:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    362d:	48 85 f6             	test   %rsi,%rsi
    3630:	7f 21                	jg     3653 <timer_thread+0x283>
    3632:	48 83 c2 01          	add    $0x1,%rdx
    3636:	48 39 d7             	cmp    %rdx,%rdi
    3639:	74 47                	je     3682 <timer_thread+0x2b2>
    363b:	48 8b 71 70          	mov    0x70(%rcx),%rsi
    363f:	48 89 d0             	mov    %rdx,%rax
    3642:	48 c1 e0 05          	shl    $0x5,%rax
    3646:	48 8b 34 06          	mov    (%rsi,%rax,1),%rsi
    364a:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    364e:	48 85 f6             	test   %rsi,%rsi
    3651:	7e cd                	jle    3620 <timer_thread+0x250>
    3653:	48 8b 71 70          	mov    0x70(%rcx),%rsi
    3657:	bf 01 00 00 00       	mov    $0x1,%edi
    365c:	48 8b 74 06 08       	mov    0x8(%rsi,%rax,1),%rsi
    3661:	4c 8b 46 08          	mov    0x8(%rsi),%r8
    3665:	48 8b 49 70          	mov    0x70(%rcx),%rcx
    3669:	48 89 ee             	mov    %rbp,%rsi
    366c:	48 8b 04 01          	mov    (%rcx,%rax,1),%rax
    3670:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3674:	31 c0                	xor    %eax,%eax
    3676:	e8 b5 ed ff ff       	call   2430 <__printf_chk@plt>
    367b:	45 8b 47 18          	mov    0x18(%r15),%r8d
    367f:	45 31 c9             	xor    %r9d,%r9d
    3682:	49 83 c6 01          	add    $0x1,%r14
    3686:	45 39 f0             	cmp    %r14d,%r8d
    3689:	0f 8f 69 ff ff ff    	jg     35f8 <timer_thread+0x228>
    368f:	41 83 c4 01          	add    $0x1,%r12d
    3693:	45 39 c4             	cmp    %r8d,%r12d
    3696:	7d 09                	jge    36a1 <timer_thread+0x2d1>
    3698:	48 83 c3 78          	add    $0x78,%rbx
    369c:	e9 4f ff ff ff       	jmp    35f0 <timer_thread+0x220>
    36a1:	41 83 f9 01          	cmp    $0x1,%r9d
    36a5:	74 17                	je     36be <timer_thread+0x2ee>
    36a7:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    36ac:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    36b1:	4d 63 f5             	movslq %r13d,%r14
    36b4:	e8 77 ec ff ff       	call   2330 <nanosleep@plt>
    36b9:	e9 9f fe ff ff       	jmp    355d <timer_thread+0x18d>
    36be:	48 8d 3d 8f 29 00 00 	lea    0x298f(%rip),%rdi        # 6054 <_IO_stdin_used+0x54>
    36c5:	48 8d 2d b4 29 00 00 	lea    0x29b4(%rip),%rbp        # 6080 <_IO_stdin_used+0x80>
    36cc:	e8 ff eb ff ff       	call   22d0 <puts@plt>
    36d1:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    36d5:	48 8d 1d 92 29 00 00 	lea    0x2992(%rip),%rbx        # 606e <_IO_stdin_used+0x6e>
    36dc:	85 c0                	test   %eax,%eax
    36de:	0f 84 b6 00 00 00    	je     379a <timer_thread+0x3ca>
    36e4:	41 8b 57 1c          	mov    0x1c(%r15),%edx
    36e8:	45 31 e4             	xor    %r12d,%r12d
    36eb:	45 31 ed             	xor    %r13d,%r13d
    36ee:	85 d2                	test   %edx,%edx
    36f0:	7e 26                	jle    3718 <timer_thread+0x348>
    36f2:	49 8b 4f 10          	mov    0x10(%r15),%rcx
    36f6:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    36fa:	83 78 04 02          	cmpl   $0x2,0x4(%rax)
    36fe:	c7 40 2c 00 00 00 00 	movl   $0x0,0x2c(%rax)
    3705:	0f 84 bc 00 00 00    	je     37c7 <timer_thread+0x3f7>
    370b:	41 83 c5 01          	add    $0x1,%r13d
    370f:	49 83 c4 78          	add    $0x78,%r12
    3713:	41 39 d5             	cmp    %edx,%r13d
    3716:	7c de                	jl     36f6 <timer_thread+0x326>
    3718:	49 63 57 18          	movslq 0x18(%r15),%rdx
    371c:	85 d2                	test   %edx,%edx
    371e:	7e 5b                	jle    377b <timer_thread+0x3ab>
    3720:	49 63 47 28          	movslq 0x28(%r15),%rax
    3724:	85 c0                	test   %eax,%eax
    3726:	7e 53                	jle    377b <timer_thread+0x3ab>
    3728:	48 89 d6             	mov    %rdx,%rsi
    372b:	4d 8b 47 10          	mov    0x10(%r15),%r8
    372f:	31 c9                	xor    %ecx,%ecx
    3731:	48 c1 e6 04          	shl    $0x4,%rsi
    3735:	48 29 d6             	sub    %rdx,%rsi
    3738:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    373c:	48 8d 3c 50          	lea    (%rax,%rdx,2),%rdi
    3740:	48 c1 e6 03          	shl    $0x3,%rsi
    3744:	48 c1 e7 03          	shl    $0x3,%rdi
    3748:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3750:	49 8b 44 08 20       	mov    0x20(%r8,%rcx,1),%rax
    3755:	48 8d 14 38          	lea    (%rax,%rdi,1),%rdx
    3759:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3760:	c7 40 48 00 00 00 00 	movl   $0x0,0x48(%rax)
    3767:	48 05 98 00 00 00    	add    $0x98,%rax
    376d:	48 39 d0             	cmp    %rdx,%rax
    3770:	75 ee                	jne    3760 <timer_thread+0x390>
    3772:	48 83 c1 78          	add    $0x78,%rcx
    3776:	48 39 f1             	cmp    %rsi,%rcx
    3779:	75 d5                	jne    3750 <timer_thread+0x380>
    377b:	0f ae f0             	mfence
    377e:	48 89 ef             	mov    %rbp,%rdi
    3781:	e8 4a eb ff ff       	call   22d0 <puts@plt>
    3786:	41 c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%r15)
    378e:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    3792:	85 c0                	test   %eax,%eax
    3794:	0f 85 4a ff ff ff    	jne    36e4 <timer_thread+0x314>
    379a:	48 8d 3d e6 28 00 00 	lea    0x28e6(%rip),%rdi        # 6087 <_IO_stdin_used+0x87>
    37a1:	e8 2a eb ff ff       	call   22d0 <puts@plt>
    37a6:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    37ab:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    37b4:	75 46                	jne    37fc <timer_thread+0x42c>
    37b6:	48 83 c4 58          	add    $0x58,%rsp
    37ba:	31 c0                	xor    %eax,%eax
    37bc:	5b                   	pop    %rbx
    37bd:	5d                   	pop    %rbp
    37be:	41 5c                	pop    %r12
    37c0:	41 5d                	pop    %r13
    37c2:	41 5e                	pop    %r14
    37c4:	41 5f                	pop    %r15
    37c6:	c3                   	ret
    37c7:	48 89 df             	mov    %rbx,%rdi
    37ca:	41 83 c5 01          	add    $0x1,%r13d
    37ce:	e8 fd ea ff ff       	call   22d0 <puts@plt>
    37d3:	49 8b 47 10          	mov    0x10(%r15),%rax
    37d7:	be 01 00 00 00       	mov    $0x1,%esi
    37dc:	42 8b 7c 20 48       	mov    0x48(%rax,%r12,1),%edi
    37e1:	49 83 c4 78          	add    $0x78,%r12
    37e5:	e8 f6 eb ff ff       	call   23e0 <eventfd_write@plt>
    37ea:	41 8b 57 1c          	mov    0x1c(%r15),%edx
    37ee:	41 39 d5             	cmp    %edx,%r13d
    37f1:	0f 8c fb fe ff ff    	jl     36f2 <timer_thread+0x322>
    37f7:	e9 1c ff ff ff       	jmp    3718 <timer_thread+0x348>
    37fc:	e8 0f eb ff ff       	call   2310 <__stack_chk_fail@plt>
    3801:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    380c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000003810 <fatal_error>:
    3810:	f3 0f 1e fa          	endbr64
    3814:	50                   	push   %rax
    3815:	58                   	pop    %rax
    3816:	48 83 ec 08          	sub    $0x8,%rsp
    381a:	e8 51 ec ff ff       	call   2470 <perror@plt>
    381f:	bf 01 00 00 00       	mov    $0x1,%edi
    3824:	e8 57 ec ff ff       	call   2480 <exit@plt>
    3829:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000003830 <strtolower>:
    3830:	f3 0f 1e fa          	endbr64
    3834:	55                   	push   %rbp
    3835:	53                   	push   %rbx
    3836:	48 83 ec 08          	sub    $0x8,%rsp
    383a:	48 0f be 1f          	movsbq (%rdi),%rbx
    383e:	84 db                	test   %bl,%bl
    3840:	74 24                	je     3866 <strtolower+0x36>
    3842:	48 89 fd             	mov    %rdi,%rbp
    3845:	e8 a6 ec ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    384a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3850:	48 8b 10             	mov    (%rax),%rdx
    3853:	48 83 c5 01          	add    $0x1,%rbp
    3857:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    385a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    385d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    3862:	84 db                	test   %bl,%bl
    3864:	75 ea                	jne    3850 <strtolower+0x20>
    3866:	48 83 c4 08          	add    $0x8,%rsp
    386a:	5b                   	pop    %rbx
    386b:	5d                   	pop    %rbp
    386c:	c3                   	ret
    386d:	0f 1f 00             	nopl   (%rax)

0000000000003870 <zh_malloc>:
    3870:	f3 0f 1e fa          	endbr64
    3874:	48 83 ec 08          	sub    $0x8,%rsp
    3878:	e8 73 eb ff ff       	call   23f0 <malloc@plt>
    387d:	48 85 c0             	test   %rax,%rax
    3880:	74 05                	je     3887 <zh_malloc+0x17>
    3882:	48 83 c4 08          	add    $0x8,%rsp
    3886:	c3                   	ret
    3887:	48 8b 0d 92 57 00 00 	mov    0x5792(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    388e:	ba 28 00 00 00       	mov    $0x28,%edx
    3893:	be 01 00 00 00       	mov    $0x1,%esi
    3898:	48 8d 3d a9 2a 00 00 	lea    0x2aa9(%rip),%rdi        # 6348 <_IO_stdin_used+0x348>
    389f:	e8 fc eb ff ff       	call   24a0 <fwrite@plt>
    38a4:	bf 01 00 00 00       	mov    $0x1,%edi
    38a9:	e8 d2 eb ff ff       	call   2480 <exit@plt>
    38ae:	66 90                	xchg   %ax,%ax

00000000000038b0 <get_filename_ext>:
    38b0:	f3 0f 1e fa          	endbr64
    38b4:	53                   	push   %rbx
    38b5:	be 2e 00 00 00       	mov    $0x2e,%esi
    38ba:	48 89 fb             	mov    %rdi,%rbx
    38bd:	e8 7e ea ff ff       	call   2340 <strrchr@plt>
    38c2:	48 85 c0             	test   %rax,%rax
    38c5:	74 11                	je     38d8 <get_filename_ext+0x28>
    38c7:	48 39 c3             	cmp    %rax,%rbx
    38ca:	74 0c                	je     38d8 <get_filename_ext+0x28>
    38cc:	48 83 c0 01          	add    $0x1,%rax
    38d0:	5b                   	pop    %rbx
    38d1:	c3                   	ret
    38d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    38d8:	48 8d 05 f0 27 00 00 	lea    0x27f0(%rip),%rax        # 60cf <_IO_stdin_used+0xcf>
    38df:	5b                   	pop    %rbx
    38e0:	c3                   	ret
    38e1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    38ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000038f0 <send_headers>:
    38f0:	f3 0f 1e fa          	endbr64
    38f4:	41 55                	push   %r13
    38f6:	49 89 f5             	mov    %rsi,%r13
    38f9:	48 89 fe             	mov    %rdi,%rsi
    38fc:	41 54                	push   %r12
    38fe:	55                   	push   %rbp
    38ff:	48 89 d5             	mov    %rdx,%rbp
    3902:	ba 00 04 00 00       	mov    $0x400,%edx
    3907:	53                   	push   %rbx
    3908:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    390f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    3918:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    3920:	31 c0                	xor    %eax,%eax
    3922:	49 89 e4             	mov    %rsp,%r12
    3925:	4c 89 e7             	mov    %r12,%rdi
    3928:	e8 e3 ea ff ff       	call   2410 <__strcpy_chk@plt>
    392d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    3932:	84 db                	test   %bl,%bl
    3934:	74 24                	je     395a <send_headers+0x6a>
    3936:	e8 b5 eb ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    393b:	48 8b 08             	mov    (%rax),%rcx
    393e:	4c 89 e0             	mov    %r12,%rax
    3941:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3948:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    394b:	48 83 c0 01          	add    $0x1,%rax
    394f:	88 50 ff             	mov    %dl,-0x1(%rax)
    3952:	48 0f be 18          	movsbq (%rax),%rbx
    3956:	84 db                	test   %bl,%bl
    3958:	75 ee                	jne    3948 <send_headers+0x58>
    395a:	bf 11 00 00 00       	mov    $0x11,%edi
    395f:	e8 8c ea ff ff       	call   23f0 <malloc@plt>
    3964:	48 85 c0             	test   %rax,%rax
    3967:	0f 84 7e 04 00 00    	je     3deb <send_headers+0x4fb>
    396d:	66 0f 6f 05 3b 2e 00 00 	movdqa 0x2e3b(%rip),%xmm0        # 67b0 <_IO_stdin_used+0x7b0>
    3975:	48 89 45 00          	mov    %rax,0x0(%rbp)
    3979:	bf 17 00 00 00       	mov    $0x17,%edi
    397e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    3986:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    398a:	0f 11 00             	movups %xmm0,(%rax)
    398d:	e8 5e ea ff ff       	call   23f0 <malloc@plt>
    3992:	48 85 c0             	test   %rax,%rax
    3995:	0f 84 50 04 00 00    	je     3deb <send_headers+0x4fb>
    399b:	66 0f 6f 05 1d 2e 00 00 	movdqa 0x2e1d(%rip),%xmm0        # 67c0 <_IO_stdin_used+0x7c0>
    39a3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    39a7:	4c 89 e7             	mov    %r12,%rdi
    39aa:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    39b4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    39bc:	0f 11 00             	movups %xmm0,(%rax)
    39bf:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    39c3:	be 2e 00 00 00       	mov    $0x2e,%esi
    39c8:	e8 73 e9 ff ff       	call   2340 <strrchr@plt>
    39cd:	48 85 c0             	test   %rax,%rax
    39d0:	0f 84 ea 02 00 00    	je     3cc0 <send_headers+0x3d0>
    39d6:	4c 39 e0             	cmp    %r12,%rax
    39d9:	0f 84 e1 02 00 00    	je     3cc0 <send_headers+0x3d0>
    39df:	48 8d 58 01          	lea    0x1(%rax),%rbx
    39e3:	48 8d 3d b3 26 00 00 	lea    0x26b3(%rip),%rdi        # 609d <_IO_stdin_used+0x9d>
    39ea:	48 89 de             	mov    %rbx,%rsi
    39ed:	e8 9e e9 ff ff       	call   2390 <strcmp@plt>
    39f2:	85 c0                	test   %eax,%eax
    39f4:	75 20                	jne    3a16 <send_headers+0x126>
    39f6:	66 0f 6f 05 d2 2d 00 00 	movdqa 0x2dd2(%rip),%xmm0        # 67d0 <_IO_stdin_used+0x7d0>
    39fe:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3a06:	66 0f 6f 05 d2 2d 00 00 	movdqa 0x2dd2(%rip),%xmm0        # 67e0 <_IO_stdin_used+0x7e0>
    3a0e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    3a16:	48 89 de             	mov    %rbx,%rsi
    3a19:	48 8d 3d 81 26 00 00 	lea    0x2681(%rip),%rdi        # 60a1 <_IO_stdin_used+0xa1>
    3a20:	e8 6b e9 ff ff       	call   2390 <strcmp@plt>
    3a25:	85 c0                	test   %eax,%eax
    3a27:	75 20                	jne    3a49 <send_headers+0x159>
    3a29:	66 0f 6f 05 9f 2d 00 00 	movdqa 0x2d9f(%rip),%xmm0        # 67d0 <_IO_stdin_used+0x7d0>
    3a31:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3a39:	66 0f 6f 05 9f 2d 00 00 	movdqa 0x2d9f(%rip),%xmm0        # 67e0 <_IO_stdin_used+0x7e0>
    3a41:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    3a49:	48 89 de             	mov    %rbx,%rsi
    3a4c:	48 8d 3d 53 26 00 00 	lea    0x2653(%rip),%rdi        # 60a6 <_IO_stdin_used+0xa6>
    3a53:	e8 38 e9 ff ff       	call   2390 <strcmp@plt>
    3a58:	85 c0                	test   %eax,%eax
    3a5a:	0f 84 10 02 00 00    	je     3c70 <send_headers+0x380>
    3a60:	48 89 de             	mov    %rbx,%rsi
    3a63:	48 8d 3d 40 26 00 00 	lea    0x2640(%rip),%rdi        # 60aa <_IO_stdin_used+0xaa>
    3a6a:	e8 21 e9 ff ff       	call   2390 <strcmp@plt>
    3a6f:	85 c0                	test   %eax,%eax
    3a71:	0f 84 a9 02 00 00    	je     3d20 <send_headers+0x430>
    3a77:	48 89 de             	mov    %rbx,%rsi
    3a7a:	48 8d 3d 2d 26 00 00 	lea    0x262d(%rip),%rdi        # 60ae <_IO_stdin_used+0xae>
    3a81:	e8 0a e9 ff ff       	call   2390 <strcmp@plt>
    3a86:	85 c0                	test   %eax,%eax
    3a88:	0f 84 6a 02 00 00    	je     3cf8 <send_headers+0x408>
    3a8e:	48 89 de             	mov    %rbx,%rsi
    3a91:	48 8d 3d 59 26 00 00 	lea    0x2659(%rip),%rdi        # 60f1 <_IO_stdin_used+0xf1>
    3a98:	e8 f3 e8 ff ff       	call   2390 <strcmp@plt>
    3a9d:	85 c0                	test   %eax,%eax
    3a9f:	0f 84 2b 02 00 00    	je     3cd0 <send_headers+0x3e0>
    3aa5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    3aa8:	0f 84 52 01 00 00    	je     3c00 <send_headers+0x310>
    3aae:	48 89 de             	mov    %rbx,%rsi
    3ab1:	48 8d 3d fa 25 00 00 	lea    0x25fa(%rip),%rdi        # 60b2 <_IO_stdin_used+0xb2>
    3ab8:	e8 d3 e8 ff ff       	call   2390 <strcmp@plt>
    3abd:	85 c0                	test   %eax,%eax
    3abf:	0f 84 ab 02 00 00    	je     3d70 <send_headers+0x480>
    3ac5:	48 89 de             	mov    %rbx,%rsi
    3ac8:	48 8d 3d e7 25 00 00 	lea    0x25e7(%rip),%rdi        # 60b6 <_IO_stdin_used+0xb6>
    3acf:	e8 bc e8 ff ff       	call   2390 <strcmp@plt>
    3ad4:	85 c0                	test   %eax,%eax
    3ad6:	0f 84 6c 02 00 00    	je     3d48 <send_headers+0x458>
    3adc:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    3ae4:	4c 89 e7             	mov    %r12,%rdi
    3ae7:	e8 14 e8 ff ff       	call   2300 <strlen@plt>
    3aec:	48 89 c7             	mov    %rax,%rdi
    3aef:	48 89 c3             	mov    %rax,%rbx
    3af2:	e8 f9 e8 ff ff       	call   23f0 <malloc@plt>
    3af7:	48 85 c0             	test   %rax,%rax
    3afa:	0f 84 eb 02 00 00    	je     3deb <send_headers+0x4fb>
    3b00:	48 89 45 20          	mov    %rax,0x20(%rbp)
    3b04:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
    3b08:	83 fb 08             	cmp    $0x8,%ebx
    3b0b:	0f 83 3f 01 00 00    	jae    3c50 <send_headers+0x360>
    3b11:	f6 c3 04             	test   $0x4,%bl
    3b14:	0f 85 7b 02 00 00    	jne    3d95 <send_headers+0x4a5>
    3b1a:	85 db                	test   %ebx,%ebx
    3b1c:	74 13                	je     3b31 <send_headers+0x241>
    3b1e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3b26:	88 10                	mov    %dl,(%rax)
    3b28:	f6 c3 02             	test   $0x2,%bl
    3b2b:	0f 85 96 02 00 00    	jne    3dc7 <send_headers+0x4d7>
    3b31:	4d 89 e8             	mov    %r13,%r8
    3b34:	48 8d 0d 7f 25 00 00 	lea    0x257f(%rip),%rcx        # 60ba <_IO_stdin_used+0xba>
    3b3b:	4c 89 e7             	mov    %r12,%rdi
    3b3e:	31 c0                	xor    %eax,%eax
    3b40:	ba 00 04 00 00       	mov    $0x400,%edx
    3b45:	be 01 00 00 00       	mov    $0x1,%esi
    3b4a:	e8 b1 e9 ff ff       	call   2500 <__sprintf_chk@plt>
    3b4f:	4c 89 e7             	mov    %r12,%rdi
    3b52:	e8 a9 e7 ff ff       	call   2300 <strlen@plt>
    3b57:	48 89 c7             	mov    %rax,%rdi
    3b5a:	48 89 c3             	mov    %rax,%rbx
    3b5d:	e8 8e e8 ff ff       	call   23f0 <malloc@plt>
    3b62:	48 85 c0             	test   %rax,%rax
    3b65:	0f 84 80 02 00 00    	je     3deb <send_headers+0x4fb>
    3b6b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    3b6f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    3b73:	83 fb 08             	cmp    $0x8,%ebx
    3b76:	0f 83 1c 01 00 00    	jae    3c98 <send_headers+0x3a8>
    3b7c:	f6 c3 04             	test   $0x4,%bl
    3b7f:	0f 85 29 02 00 00    	jne    3dae <send_headers+0x4be>
    3b85:	85 db                	test   %ebx,%ebx
    3b87:	74 13                	je     3b9c <send_headers+0x2ac>
    3b89:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    3b91:	88 10                	mov    %dl,(%rax)
    3b93:	f6 c3 02             	test   $0x2,%bl
    3b96:	0f 85 3d 02 00 00    	jne    3dd9 <send_headers+0x4e9>
    3b9c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    3ba1:	bf 02 00 00 00       	mov    $0x2,%edi
    3ba6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    3bae:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    3bb6:	e8 35 e8 ff ff       	call   23f0 <malloc@plt>
    3bbb:	48 85 c0             	test   %rax,%rax
    3bbe:	0f 84 27 02 00 00    	je     3deb <send_headers+0x4fb>
    3bc4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    3bcc:	48 89 45 40          	mov    %rax,0x40(%rbp)
    3bd0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    3bd8:	66 89 10             	mov    %dx,(%rax)
    3bdb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    3be3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    3bec:	0f 85 20 02 00 00    	jne    3e12 <send_headers+0x522>
    3bf2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    3bf9:	5b                   	pop    %rbx
    3bfa:	5d                   	pop    %rbp
    3bfb:	41 5c                	pop    %r12
    3bfd:	41 5d                	pop    %r13
    3bff:	c3                   	ret
    3c00:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    3c04:	0f 85 a4 fe ff ff    	jne    3aae <send_headers+0x1be>
    3c0a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    3c0e:	0f 85 9a fe ff ff    	jne    3aae <send_headers+0x1be>
    3c14:	66 0f 6f 05 14 2c 00 00 	movdqa 0x2c14(%rip),%xmm0        # 6830 <_IO_stdin_used+0x830>
    3c1c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    3c26:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3c2e:	66 0f 6f 05 0a 2c 00 00 	movdqa 0x2c0a(%rip),%xmm0        # 6840 <_IO_stdin_used+0x840>
    3c36:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    3c3e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    3c46:	e9 63 fe ff ff       	jmp    3aae <send_headers+0x1be>
    3c4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3c50:	89 da                	mov    %ebx,%edx
    3c52:	48 89 c7             	mov    %rax,%rdi
    3c55:	4c 89 e6             	mov    %r12,%rsi
    3c58:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    3c5d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    3c62:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    3c65:	c1 e9 03             	shr    $0x3,%ecx
    3c68:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    3c6b:	e9 c1 fe ff ff       	jmp    3b31 <send_headers+0x241>
    3c70:	66 0f 6f 05 58 2b 00 00 	movdqa 0x2b58(%rip),%xmm0        # 67d0 <_IO_stdin_used+0x7d0>
    3c78:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3c80:	66 0f 6f 05 68 2b 00 00 	movdqa 0x2b68(%rip),%xmm0        # 67f0 <_IO_stdin_used+0x7f0>
    3c88:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    3c90:	e9 cb fd ff ff       	jmp    3a60 <send_headers+0x170>
    3c95:	0f 1f 00             	nopl   (%rax)
    3c98:	89 da                	mov    %ebx,%edx
    3c9a:	48 89 c7             	mov    %rax,%rdi
    3c9d:	4c 89 e6             	mov    %r12,%rsi
    3ca0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    3ca5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    3caa:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    3cad:	c1 e9 03             	shr    $0x3,%ecx
    3cb0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    3cb3:	e9 e4 fe ff ff       	jmp    3b9c <send_headers+0x2ac>
    3cb8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3cc0:	48 8d 1d 08 24 00 00 	lea    0x2408(%rip),%rbx        # 60cf <_IO_stdin_used+0xcf>
    3cc7:	e9 94 fd ff ff       	jmp    3a60 <send_headers+0x170>
    3ccc:	0f 1f 40 00          	nopl   0x0(%rax)
    3cd0:	66 0f 6f 05 38 2b 00 00 	movdqa 0x2b38(%rip),%xmm0        # 6810 <_IO_stdin_used+0x810>
    3cd8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3ce0:	66 0f 6f 05 38 2b 00 00 	movdqa 0x2b38(%rip),%xmm0        # 6820 <_IO_stdin_used+0x820>
    3ce8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    3cf0:	e9 b0 fd ff ff       	jmp    3aa5 <send_headers+0x1b5>
    3cf5:	0f 1f 00             	nopl   (%rax)
    3cf8:	66 0f 6f 05 10 2b 00 00 	movdqa 0x2b10(%rip),%xmm0        # 6810 <_IO_stdin_used+0x810>
    3d00:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3d08:	66 0f 6f 05 10 2b 00 00 	movdqa 0x2b10(%rip),%xmm0        # 6820 <_IO_stdin_used+0x820>
    3d10:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    3d18:	e9 71 fd ff ff       	jmp    3a8e <send_headers+0x19e>
    3d1d:	0f 1f 00             	nopl   (%rax)
    3d20:	66 0f 6f 05 a8 2a 00 00 	movdqa 0x2aa8(%rip),%xmm0        # 67d0 <_IO_stdin_used+0x7d0>
    3d28:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3d30:	66 0f 6f 05 c8 2a 00 00 	movdqa 0x2ac8(%rip),%xmm0        # 6800 <_IO_stdin_used+0x800>
    3d38:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    3d40:	e9 32 fd ff ff       	jmp    3a77 <send_headers+0x187>
    3d45:	0f 1f 00             	nopl   (%rax)
    3d48:	66 0f 6f 05 c0 2a 00 00 	movdqa 0x2ac0(%rip),%xmm0        # 6810 <_IO_stdin_used+0x810>
    3d50:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3d58:	66 0f 6f 05 00 2b 00 00 	movdqa 0x2b00(%rip),%xmm0        # 6860 <_IO_stdin_used+0x860>
    3d60:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    3d68:	e9 6f fd ff ff       	jmp    3adc <send_headers+0x1ec>
    3d6d:	0f 1f 00             	nopl   (%rax)
    3d70:	66 0f 6f 05 98 2a 00 00 	movdqa 0x2a98(%rip),%xmm0        # 6810 <_IO_stdin_used+0x810>
    3d78:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    3d80:	66 0f 6f 05 c8 2a 00 00 	movdqa 0x2ac8(%rip),%xmm0        # 6850 <_IO_stdin_used+0x850>
    3d88:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    3d90:	e9 30 fd ff ff       	jmp    3ac5 <send_headers+0x1d5>
    3d95:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    3d9c:	89 db                	mov    %ebx,%ebx
    3d9e:	89 10                	mov    %edx,(%rax)
    3da0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    3da5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    3da9:	e9 83 fd ff ff       	jmp    3b31 <send_headers+0x241>
    3dae:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    3db5:	89 db                	mov    %ebx,%ebx
    3db7:	89 10                	mov    %edx,(%rax)
    3db9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    3dbe:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    3dc2:	e9 d5 fd ff ff       	jmp    3b9c <send_headers+0x2ac>
    3dc7:	89 db                	mov    %ebx,%ebx
    3dc9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    3dcf:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    3dd4:	e9 58 fd ff ff       	jmp    3b31 <send_headers+0x241>
    3dd9:	89 db                	mov    %ebx,%ebx
    3ddb:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    3de1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    3de6:	e9 b1 fd ff ff       	jmp    3b9c <send_headers+0x2ac>
    3deb:	48 8b 0d 2e 52 00 00 	mov    0x522e(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    3df2:	ba 28 00 00 00       	mov    $0x28,%edx
    3df7:	be 01 00 00 00       	mov    $0x1,%esi
    3dfc:	48 8d 3d 45 25 00 00 	lea    0x2545(%rip),%rdi        # 6348 <_IO_stdin_used+0x348>
    3e03:	e8 98 e6 ff ff       	call   24a0 <fwrite@plt>
    3e08:	bf 01 00 00 00       	mov    $0x1,%edi
    3e0d:	e8 6e e6 ff ff       	call   2480 <exit@plt>
    3e12:	e8 f9 e4 ff ff       	call   2310 <__stack_chk_fail@plt>
    3e17:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000003e20 <copy_file_contents>:
    3e20:	f3 0f 1e fa          	endbr64
    3e24:	41 55                	push   %r13
    3e26:	49 89 d5             	mov    %rdx,%r13
    3e29:	41 54                	push   %r12
    3e2b:	49 89 fc             	mov    %rdi,%r12
    3e2e:	48 89 f7             	mov    %rsi,%rdi
    3e31:	55                   	push   %rbp
    3e32:	53                   	push   %rbx
    3e33:	48 89 f3             	mov    %rsi,%rbx
    3e36:	48 83 ec 08          	sub    $0x8,%rsp
    3e3a:	e8 b1 e5 ff ff       	call   23f0 <malloc@plt>
    3e3f:	48 85 c0             	test   %rax,%rax
    3e42:	74 77                	je     3ebb <copy_file_contents+0x9b>
    3e44:	4c 89 e7             	mov    %r12,%rdi
    3e47:	48 89 c5             	mov    %rax,%rbp
    3e4a:	31 f6                	xor    %esi,%esi
    3e4c:	31 c0                	xor    %eax,%eax
    3e4e:	e8 0d e6 ff ff       	call   2460 <open@plt>
    3e53:	41 89 c4             	mov    %eax,%r12d
    3e56:	85 c0                	test   %eax,%eax
    3e58:	78 55                	js     3eaf <copy_file_contents+0x8f>
    3e5a:	48 89 da             	mov    %rbx,%rdx
    3e5d:	48 89 ee             	mov    %rbp,%rsi
    3e60:	89 c7                	mov    %eax,%edi
    3e62:	e8 09 e5 ff ff       	call   2370 <read@plt>
    3e67:	48 98                	cltq
    3e69:	48 39 d8             	cmp    %rbx,%rax
    3e6c:	7c 22                	jl     3e90 <copy_file_contents+0x70>
    3e6e:	44 89 e7             	mov    %r12d,%edi
    3e71:	e8 da e4 ff ff       	call   2350 <close@plt>
    3e76:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    3e7a:	49 89 5d 08          	mov    %rbx,0x8(%r13)
    3e7e:	48 83 c4 08          	add    $0x8,%rsp
    3e82:	5b                   	pop    %rbx
    3e83:	5d                   	pop    %rbp
    3e84:	41 5c                	pop    %r12
    3e86:	41 5d                	pop    %r13
    3e88:	c3                   	ret
    3e89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3e90:	48 8b 0d 89 51 00 00 	mov    0x5189(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    3e97:	ba 1a 00 00 00       	mov    $0x1a,%edx
    3e9c:	be 01 00 00 00       	mov    $0x1,%esi
    3ea1:	48 8d 3d 28 22 00 00 	lea    0x2228(%rip),%rdi        # 60d0 <_IO_stdin_used+0xd0>
    3ea8:	e8 f3 e5 ff ff       	call   24a0 <fwrite@plt>
    3ead:	eb bf                	jmp    3e6e <copy_file_contents+0x4e>
    3eaf:	48 8d 3d 49 23 00 00 	lea    0x2349(%rip),%rdi        # 61ff <_IO_stdin_used+0x1ff>
    3eb6:	e8 55 f9 ff ff       	call   3810 <fatal_error>
    3ebb:	48 8b 0d 5e 51 00 00 	mov    0x515e(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    3ec2:	ba 28 00 00 00       	mov    $0x28,%edx
    3ec7:	be 01 00 00 00       	mov    $0x1,%esi
    3ecc:	48 8d 3d 75 24 00 00 	lea    0x2475(%rip),%rdi        # 6348 <_IO_stdin_used+0x348>
    3ed3:	e8 c8 e5 ff ff       	call   24a0 <fwrite@plt>
    3ed8:	bf 01 00 00 00       	mov    $0x1,%edi
    3edd:	e8 9e e5 ff ff       	call   2480 <exit@plt>
    3ee2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    3eed:	0f 1f 00             	nopl   (%rax)

0000000000003ef0 <add_write_request>:
    3ef0:	f3 0f 1e fa          	endbr64
    3ef4:	8b 46 44             	mov    0x44(%rsi),%eax
    3ef7:	48 89 fa             	mov    %rdi,%rdx
    3efa:	48 89 f7             	mov    %rsi,%rdi
    3efd:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    3f03:	8d 70 01             	lea    0x1(%rax),%esi
    3f06:	48 8b 07             	mov    (%rdi),%rax
    3f09:	44 8b 00             	mov    (%rax),%r8d
    3f0c:	f6 c1 02             	test   $0x2,%cl
    3f0f:	74 00                	je     3f11 <add_write_request+0x21>
    3f11:	89 f0                	mov    %esi,%eax
    3f13:	44 29 c0             	sub    %r8d,%eax
    3f16:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    3f19:	0f 82 01 e6 ff ff    	jb     2520 <add_write_request.cold>
    3f1f:	c1 e9 0a             	shr    $0xa,%ecx
    3f22:	48 83 ec 08          	sub    $0x8,%rsp
    3f26:	8b 47 44             	mov    0x44(%rdi),%eax
    3f29:	23 47 58             	and    0x58(%rdi),%eax
    3f2c:	83 e1 01             	and    $0x1,%ecx
    3f2f:	89 77 44             	mov    %esi,0x44(%rdi)
    3f32:	8b 72 08             	mov    0x8(%rdx),%esi
    3f35:	66 0f ef c0          	pxor   %xmm0,%xmm0
    3f39:	d3 e0                	shl    %cl,%eax
    3f3b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    3f3e:	48 c1 e0 06          	shl    $0x6,%rax
    3f42:	48 03 47 38          	add    0x38(%rdi),%rax
    3f46:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    3f4c:	89 70 04             	mov    %esi,0x4(%rax)
    3f4f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
    3f53:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    3f59:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    3f61:	48 89 70 10          	mov    %rsi,0x10(%rax)
    3f65:	89 48 18             	mov    %ecx,0x18(%rax)
    3f68:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    3f6f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    3f77:	48 89 50 20          	mov    %rdx,0x20(%rax)
    3f7b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    3f7f:	e8 9c e3 ff ff       	call   2320 <io_uring_submit@plt>
    3f84:	31 c0                	xor    %eax,%eax
    3f86:	48 83 c4 08          	add    $0x8,%rsp
    3f8a:	c3                   	ret
    3f8b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000003f90 <add_read_request>:
    3f90:	f3 0f 1e fa          	endbr64
    3f94:	41 55                	push   %r13
    3f96:	41 89 fd             	mov    %edi,%r13d
    3f99:	41 54                	push   %r12
    3f9b:	55                   	push   %rbp
    3f9c:	53                   	push   %rbx
    3f9d:	48 89 f3             	mov    %rsi,%rbx
    3fa0:	48 83 ec 08          	sub    $0x8,%rsp
    3fa4:	8b 46 44             	mov    0x44(%rsi),%eax
    3fa7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
    3fad:	48 8b 16             	mov    (%rsi),%rdx
    3fb0:	83 c0 01             	add    $0x1,%eax
    3fb3:	8b 32                	mov    (%rdx),%esi
    3fb5:	f6 c1 02             	test   $0x2,%cl
    3fb8:	74 00                	je     3fba <add_read_request+0x2a>
    3fba:	89 c2                	mov    %eax,%edx
    3fbc:	29 f2                	sub    %esi,%edx
    3fbe:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    3fc1:	0f 82 69 e5 ff ff    	jb     2530 <add_read_request.cold>
    3fc7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    3fca:	c1 e9 0a             	shr    $0xa,%ecx
    3fcd:	89 43 44             	mov    %eax,0x44(%rbx)
    3fd0:	bf 20 00 00 00       	mov    $0x20,%edi
    3fd5:	83 e1 01             	and    $0x1,%ecx
    3fd8:	23 6b 58             	and    0x58(%rbx),%ebp
    3fdb:	d3 e5                	shl    %cl,%ebp
    3fdd:	48 c1 e5 06          	shl    $0x6,%rbp
    3fe1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    3fe5:	e8 06 e4 ff ff       	call   23f0 <malloc@plt>
    3fea:	be 01 00 00 00       	mov    $0x1,%esi
    3fef:	bf 00 20 00 00       	mov    $0x2000,%edi
    3ff4:	49 89 c4             	mov    %rax,%r12
    3ff7:	e8 84 e3 ff ff       	call   2380 <calloc@plt>
    3ffc:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    4001:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4005:	48 89 df             	mov    %rbx,%rdi
    4008:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    400d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    4012:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    401b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    4023:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
    4027:	4c 89 65 20          	mov    %r12,0x20(%rbp)
    402b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
    4032:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    403a:	48 89 45 10          	mov    %rax,0x10(%rbp)
    403e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
    4046:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    404e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    4052:	e8 c9 e2 ff ff       	call   2320 <io_uring_submit@plt>
    4057:	48 83 c4 08          	add    $0x8,%rsp
    405b:	31 c0                	xor    %eax,%eax
    405d:	5b                   	pop    %rbx
    405e:	5d                   	pop    %rbp
    405f:	41 5c                	pop    %r12
    4061:	41 5d                	pop    %r13
    4063:	c3                   	ret
    4064:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    406f:	90                   	nop

0000000000004070 <_send_static_string_content>:
    4070:	f3 0f 1e fa          	endbr64
    4074:	41 56                	push   %r14
    4076:	41 89 f6             	mov    %esi,%r14d
    4079:	41 55                	push   %r13
    407b:	49 89 fd             	mov    %rdi,%r13
    407e:	bf 20 00 00 00       	mov    $0x20,%edi
    4083:	41 54                	push   %r12
    4085:	55                   	push   %rbp
    4086:	48 89 d5             	mov    %rdx,%rbp
    4089:	53                   	push   %rbx
    408a:	e8 61 e3 ff ff       	call   23f0 <malloc@plt>
    408f:	48 85 c0             	test   %rax,%rax
    4092:	0f 84 dd 00 00 00    	je     4175 <_send_static_string_content+0x105>
    4098:	48 89 c3             	mov    %rax,%rbx
    409b:	4c 89 ef             	mov    %r13,%rdi
    409e:	e8 5d e2 ff ff       	call   2300 <strlen@plt>
    40a3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    40aa:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    40ae:	48 89 c7             	mov    %rax,%rdi
    40b1:	49 89 c4             	mov    %rax,%r12
    40b4:	e8 37 e3 ff ff       	call   23f0 <malloc@plt>
    40b9:	48 89 c7             	mov    %rax,%rdi
    40bc:	48 85 c0             	test   %rax,%rax
    40bf:	0f 84 b0 00 00 00    	je     4175 <_send_static_string_content+0x105>
    40c5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    40c9:	4c 89 e2             	mov    %r12,%rdx
    40cc:	4c 89 ee             	mov    %r13,%rsi
    40cf:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    40d3:	e8 e8 e2 ff ff       	call   23c0 <memcpy@plt>
    40d8:	8b 45 44             	mov    0x44(%rbp),%eax
    40db:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
    40e1:	8d 50 01             	lea    0x1(%rax),%edx
    40e4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    40e8:	8b 30                	mov    (%rax),%esi
    40ea:	f6 c1 02             	test   $0x2,%cl
    40ed:	0f 85 7d 00 00 00    	jne    4170 <_send_static_string_content+0x100>
    40f3:	89 d0                	mov    %edx,%eax
    40f5:	29 f0                	sub    %esi,%eax
    40f7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    40fa:	0f 82 3a e4 ff ff    	jb     253a <_send_static_string_content.cold>
    4100:	c1 e9 0a             	shr    $0xa,%ecx
    4103:	8b 45 44             	mov    0x44(%rbp),%eax
    4106:	23 45 58             	and    0x58(%rbp),%eax
    4109:	89 55 44             	mov    %edx,0x44(%rbp)
    410c:	83 e1 01             	and    $0x1,%ecx
    410f:	8b 53 04             	mov    0x4(%rbx),%edx
    4112:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    4118:	66 0f ef c0          	pxor   %xmm0,%xmm0
    411c:	d3 e0                	shl    %cl,%eax
    411e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    4121:	48 89 ef             	mov    %rbp,%rdi
    4124:	48 c1 e0 06          	shl    $0x6,%rax
    4128:	48 03 45 38          	add    0x38(%rbp),%rax
    412c:	89 48 04             	mov    %ecx,0x4(%rax)
    412f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
    4133:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    4139:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4141:	48 89 48 10          	mov    %rcx,0x10(%rax)
    4145:	89 50 18             	mov    %edx,0x18(%rax)
    4148:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    414f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4157:	48 89 58 20          	mov    %rbx,0x20(%rax)
    415b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    415f:	5b                   	pop    %rbx
    4160:	5d                   	pop    %rbp
    4161:	41 5c                	pop    %r12
    4163:	41 5d                	pop    %r13
    4165:	41 5e                	pop    %r14
    4167:	e9 b4 e1 ff ff       	jmp    2320 <io_uring_submit@plt>
    416c:	0f 1f 40 00          	nopl   0x0(%rax)
    4170:	e9 7e ff ff ff       	jmp    40f3 <_send_static_string_content+0x83>
    4175:	48 8b 0d a4 4e 00 00 	mov    0x4ea4(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    417c:	ba 28 00 00 00       	mov    $0x28,%edx
    4181:	be 01 00 00 00       	mov    $0x1,%esi
    4186:	48 8d 3d bb 21 00 00 	lea    0x21bb(%rip),%rdi        # 6348 <_IO_stdin_used+0x348>
    418d:	e8 0e e3 ff ff       	call   24a0 <fwrite@plt>
    4192:	bf 01 00 00 00       	mov    $0x1,%edi
    4197:	e8 e4 e2 ff ff       	call   2480 <exit@plt>
    419c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000041a0 <handle_unimplemented_method>:
    41a0:	f3 0f 1e fa          	endbr64
    41a4:	48 89 f2             	mov    %rsi,%rdx
    41a7:	89 fe                	mov    %edi,%esi
    41a9:	48 8b 3d 68 4e 00 00 	mov    0x4e68(%rip),%rdi        # 9018 <unimplemented_content>
    41b0:	e9 bb fe ff ff       	jmp    4070 <_send_static_string_content>
    41b5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000041c0 <handle_http_404>:
    41c0:	f3 0f 1e fa          	endbr64
    41c4:	48 89 f2             	mov    %rsi,%rdx
    41c7:	89 fe                	mov    %edi,%esi
    41c9:	48 8b 3d 40 4e 00 00 	mov    0x4e40(%rip),%rdi        # 9010 <http_404_content>
    41d0:	e9 9b fe ff ff       	jmp    4070 <_send_static_string_content>
    41d5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000041e0 <handle_get_method>:
    41e0:	f3 0f 1e fa          	endbr64
    41e4:	41 56                	push   %r14
    41e6:	41 55                	push   %r13
    41e8:	49 89 d5             	mov    %rdx,%r13
    41eb:	41 54                	push   %r12
    41ed:	41 89 f4             	mov    %esi,%r12d
    41f0:	55                   	push   %rbp
    41f1:	48 89 fd             	mov    %rdi,%rbp
    41f4:	53                   	push   %rbx
    41f5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    41fc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4205:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    420d:	31 c0                	xor    %eax,%eax
    420f:	e8 ec e0 ff ff       	call   2300 <strlen@plt>
    4214:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    4219:	48 89 c3             	mov    %rax,%rbx
    421c:	0f 84 b6 00 00 00    	je     42d8 <handle_get_method+0xf8>
    4222:	b8 69 63 00 00       	mov    $0x6369,%eax
    4227:	48 89 ee             	mov    %rbp,%rsi
    422a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    422e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4233:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    423b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4243:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    424e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
    4256:	e8 45 e1 ff ff       	call   23a0 <__memcpy_chk@plt>
    425b:	48 89 e6             	mov    %rsp,%rsi
    425e:	4c 89 f7             	mov    %r14,%rdi
    4261:	e8 4a e1 ff ff       	call   23b0 <stat@plt>
    4266:	83 f8 ff             	cmp    $0xffffffff,%eax
    4269:	0f 84 d3 00 00 00    	je     4342 <handle_get_method+0x162>
    426f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    4273:	25 00 f0 00 00       	and    $0xf000,%eax
    4278:	3d 00 80 00 00       	cmp    $0x8000,%eax
    427d:	0f 84 f5 00 00 00    	je     4378 <handle_get_method+0x198>
    4283:	48 8b 3d 86 4d 00 00 	mov    0x4d86(%rip),%rdi        # 9010 <http_404_content>
    428a:	4c 89 ea             	mov    %r13,%rdx
    428d:	44 89 e6             	mov    %r12d,%esi
    4290:	e8 db fd ff ff       	call   4070 <_send_static_string_content>
    4295:	4c 89 f2             	mov    %r14,%rdx
    4298:	bf 01 00 00 00       	mov    $0x1,%edi
    429d:	31 c0                	xor    %eax,%eax
    429f:	48 8d 35 7a 1e 00 00 	lea    0x1e7a(%rip),%rsi        # 6120 <_IO_stdin_used+0x120>
    42a6:	e8 85 e1 ff ff       	call   2430 <__printf_chk@plt>
    42ab:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    42b3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    42bc:	0f 85 20 01 00 00    	jne    43e2 <handle_get_method+0x202>
    42c2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    42c9:	5b                   	pop    %rbx
    42ca:	5d                   	pop    %rbp
    42cb:	41 5c                	pop    %r12
    42cd:	41 5d                	pop    %r13
    42cf:	41 5e                	pop    %r14
    42d1:	c3                   	ret
    42d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    42d8:	ba 69 63 00 00       	mov    $0x6369,%edx
    42dd:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    42e5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    42ea:	48 89 ee             	mov    %rbp,%rsi
    42ed:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
    42f5:	48 89 c2             	mov    %rax,%rdx
    42f8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    4300:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    430b:	e8 90 e0 ff ff       	call   23a0 <__memcpy_chk@plt>
    4310:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    4315:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    431a:	48 8d 35 ca 1d 00 00 	lea    0x1dca(%rip),%rsi        # 60eb <_IO_stdin_used+0xeb>
    4321:	48 29 d9             	sub    %rbx,%rcx
    4324:	ba 0b 00 00 00       	mov    $0xb,%edx
    4329:	e8 72 e0 ff ff       	call   23a0 <__memcpy_chk@plt>
    432e:	48 89 e6             	mov    %rsp,%rsi
    4331:	4c 89 f7             	mov    %r14,%rdi
    4334:	e8 77 e0 ff ff       	call   23b0 <stat@plt>
    4339:	83 f8 ff             	cmp    $0xffffffff,%eax
    433c:	0f 85 2d ff ff ff    	jne    426f <handle_get_method+0x8f>
    4342:	4c 89 f2             	mov    %r14,%rdx
    4345:	48 89 e9             	mov    %rbp,%rcx
    4348:	48 8d 35 a7 1d 00 00 	lea    0x1da7(%rip),%rsi        # 60f6 <_IO_stdin_used+0xf6>
    434f:	31 c0                	xor    %eax,%eax
    4351:	bf 01 00 00 00       	mov    $0x1,%edi
    4356:	e8 d5 e0 ff ff       	call   2430 <__printf_chk@plt>
    435b:	48 8b 3d ae 4c 00 00 	mov    0x4cae(%rip),%rdi        # 9010 <http_404_content>
    4362:	4c 89 ea             	mov    %r13,%rdx
    4365:	44 89 e6             	mov    %r12d,%esi
    4368:	e8 03 fd ff ff       	call   4070 <_send_static_string_content>
    436d:	e9 39 ff ff ff       	jmp    42ab <handle_get_method+0xcb>
    4372:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4378:	bf 70 00 00 00       	mov    $0x70,%edi
    437d:	e8 6e e0 ff ff       	call   23f0 <malloc@plt>
    4382:	48 89 c3             	mov    %rax,%rbx
    4385:	48 85 c0             	test   %rax,%rax
    4388:	74 5d                	je     43e7 <handle_get_method+0x207>
    438a:	44 89 60 08          	mov    %r12d,0x8(%rax)
    438e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    4393:	48 8d 50 10          	lea    0x10(%rax),%rdx
    4397:	4c 89 f7             	mov    %r14,%rdi
    439a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
    43a1:	e8 4a f5 ff ff       	call   38f0 <send_headers>
    43a6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    43ab:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    43af:	4c 89 f7             	mov    %r14,%rdi
    43b2:	e8 69 fa ff ff       	call   3e20 <copy_file_contents>
    43b7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    43bc:	4c 89 f2             	mov    %r14,%rdx
    43bf:	31 c0                	xor    %eax,%eax
    43c1:	48 8d 35 46 1d 00 00 	lea    0x1d46(%rip),%rsi        # 610e <_IO_stdin_used+0x10e>
    43c8:	bf 01 00 00 00       	mov    $0x1,%edi
    43cd:	e8 5e e0 ff ff       	call   2430 <__printf_chk@plt>
    43d2:	4c 89 ee             	mov    %r13,%rsi
    43d5:	48 89 df             	mov    %rbx,%rdi
    43d8:	e8 13 fb ff ff       	call   3ef0 <add_write_request>
    43dd:	e9 c9 fe ff ff       	jmp    42ab <handle_get_method+0xcb>
    43e2:	e8 29 df ff ff       	call   2310 <__stack_chk_fail@plt>
    43e7:	48 8b 0d 32 4c 00 00 	mov    0x4c32(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    43ee:	ba 28 00 00 00       	mov    $0x28,%edx
    43f3:	be 01 00 00 00       	mov    $0x1,%esi
    43f8:	48 8d 3d 49 1f 00 00 	lea    0x1f49(%rip),%rdi        # 6348 <_IO_stdin_used+0x348>
    43ff:	e8 9c e0 ff ff       	call   24a0 <fwrite@plt>
    4404:	bf 01 00 00 00       	mov    $0x1,%edi
    4409:	e8 72 e0 ff ff       	call   2480 <exit@plt>
    440e:	66 90                	xchg   %ax,%ax

0000000000004410 <handle_http_method>:
    4410:	f3 0f 1e fa          	endbr64
    4414:	41 57                	push   %r15
    4416:	41 56                	push   %r14
    4418:	4c 8d 35 66 1c 00 00 	lea    0x1c66(%rip),%r14        # 6085 <_IO_stdin_used+0x85>
    441f:	41 55                	push   %r13
    4421:	49 89 d5             	mov    %rdx,%r13
    4424:	41 54                	push   %r12
    4426:	41 89 f4             	mov    %esi,%r12d
    4429:	4c 89 f6             	mov    %r14,%rsi
    442c:	55                   	push   %rbp
    442d:	53                   	push   %rbx
    442e:	48 83 ec 18          	sub    $0x18,%rsp
    4432:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    443b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    4440:	31 c0                	xor    %eax,%eax
    4442:	49 89 e7             	mov    %rsp,%r15
    4445:	4c 89 fa             	mov    %r15,%rdx
    4448:	e8 13 df ff ff       	call   2360 <strtok_r@plt>
    444d:	48 0f be 18          	movsbq (%rax),%rbx
    4451:	48 89 c5             	mov    %rax,%rbp
    4454:	84 db                	test   %bl,%bl
    4456:	74 1d                	je     4475 <handle_http_method+0x65>
    4458:	e8 93 e0 ff ff       	call   24f0 <__ctype_tolower_loc@plt>
    445d:	48 89 ea             	mov    %rbp,%rdx
    4460:	48 8b 08             	mov    (%rax),%rcx
    4463:	48 83 c2 01          	add    $0x1,%rdx
    4467:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    446a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    446d:	48 0f be 1a          	movsbq (%rdx),%rbx
    4471:	84 db                	test   %bl,%bl
    4473:	75 eb                	jne    4460 <handle_http_method+0x50>
    4475:	4c 89 fa             	mov    %r15,%rdx
    4478:	4c 89 f6             	mov    %r14,%rsi
    447b:	31 ff                	xor    %edi,%edi
    447d:	e8 de de ff ff       	call   2360 <strtok_r@plt>
    4482:	48 8d 35 aa 1c 00 00 	lea    0x1caa(%rip),%rsi        # 6133 <_IO_stdin_used+0x133>
    4489:	48 89 ef             	mov    %rbp,%rdi
    448c:	48 89 c3             	mov    %rax,%rbx
    448f:	e8 fc de ff ff       	call   2390 <strcmp@plt>
    4494:	4c 89 ea             	mov    %r13,%rdx
    4497:	44 89 e6             	mov    %r12d,%esi
    449a:	85 c0                	test   %eax,%eax
    449c:	75 2a                	jne    44c8 <handle_http_method+0xb8>
    449e:	48 89 df             	mov    %rbx,%rdi
    44a1:	e8 3a fd ff ff       	call   41e0 <handle_get_method>
    44a6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    44ab:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    44b4:	75 20                	jne    44d6 <handle_http_method+0xc6>
    44b6:	48 83 c4 18          	add    $0x18,%rsp
    44ba:	5b                   	pop    %rbx
    44bb:	5d                   	pop    %rbp
    44bc:	41 5c                	pop    %r12
    44be:	41 5d                	pop    %r13
    44c0:	41 5e                	pop    %r14
    44c2:	41 5f                	pop    %r15
    44c4:	c3                   	ret
    44c5:	0f 1f 00             	nopl   (%rax)
    44c8:	48 8b 3d 49 4b 00 00 	mov    0x4b49(%rip),%rdi        # 9018 <unimplemented_content>
    44cf:	e8 9c fb ff ff       	call   4070 <_send_static_string_content>
    44d4:	eb d0                	jmp    44a6 <handle_http_method+0x96>
    44d6:	e8 35 de ff ff       	call   2310 <__stack_chk_fail@plt>
    44db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000044e0 <get_line>:
    44e0:	f3 0f 1e fa          	endbr64
    44e4:	85 d2                	test   %edx,%edx
    44e6:	7e 38                	jle    4520 <get_line+0x40>
    44e8:	48 63 d2             	movslq %edx,%rdx
    44eb:	48 83 c7 01          	add    $0x1,%rdi
    44ef:	48 01 f2             	add    %rsi,%rdx
    44f2:	eb 11                	jmp    4505 <get_line+0x25>
    44f4:	0f 1f 40 00          	nopl   0x0(%rax)
    44f8:	48 83 c6 01          	add    $0x1,%rsi
    44fc:	48 83 c7 01          	add    $0x1,%rdi
    4500:	48 39 d6             	cmp    %rdx,%rsi
    4503:	74 1b                	je     4520 <get_line+0x40>
    4505:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    4509:	88 06                	mov    %al,(%rsi)
    450b:	3c 0d                	cmp    $0xd,%al
    450d:	75 e9                	jne    44f8 <get_line+0x18>
    450f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    4512:	75 e4                	jne    44f8 <get_line+0x18>
    4514:	c6 06 00             	movb   $0x0,(%rsi)
    4517:	31 c0                	xor    %eax,%eax
    4519:	c3                   	ret
    451a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4520:	b8 01 00 00 00       	mov    $0x1,%eax
    4525:	c3                   	ret
    4526:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004530 <handle_client_request>:
    4530:	f3 0f 1e fa          	endbr64
    4534:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    453b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    453f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4548:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    4550:	31 c0                	xor    %eax,%eax
    4552:	49 89 e2             	mov    %rsp,%r10
    4555:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    455d:	4c 89 d0             	mov    %r10,%rax
    4560:	eb 13                	jmp    4575 <handle_client_request+0x45>
    4562:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4568:	48 83 c0 01          	add    $0x1,%rax
    456c:	48 83 c1 01          	add    $0x1,%rcx
    4570:	4c 39 c8             	cmp    %r9,%rax
    4573:	74 4b                	je     45c0 <handle_client_request+0x90>
    4575:	44 0f b6 01          	movzbl (%rcx),%r8d
    4579:	44 88 00             	mov    %r8b,(%rax)
    457c:	41 80 f8 0d          	cmp    $0xd,%r8b
    4580:	75 e6                	jne    4568 <handle_client_request+0x38>
    4582:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    4586:	75 e0                	jne    4568 <handle_client_request+0x38>
    4588:	c6 00 00             	movb   $0x0,(%rax)
    458b:	8b 47 08             	mov    0x8(%rdi),%eax
    458e:	48 89 f2             	mov    %rsi,%rdx
    4591:	4c 89 d7             	mov    %r10,%rdi
    4594:	89 c6                	mov    %eax,%esi
    4596:	e8 75 fe ff ff       	call   4410 <handle_http_method>
    459b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    45a3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    45ac:	75 39                	jne    45e7 <handle_client_request+0xb7>
    45ae:	31 c0                	xor    %eax,%eax
    45b0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    45b7:	c3                   	ret
    45b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    45c0:	48 8b 0d 59 4a 00 00 	mov    0x4a59(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    45c7:	ba 12 00 00 00       	mov    $0x12,%edx
    45cc:	be 01 00 00 00       	mov    $0x1,%esi
    45d1:	48 8d 3d 5f 1b 00 00 	lea    0x1b5f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    45d8:	e8 c3 de ff ff       	call   24a0 <fwrite@plt>
    45dd:	bf 01 00 00 00       	mov    $0x1,%edi
    45e2:	e8 99 de ff ff       	call   2480 <exit@plt>
    45e7:	e8 24 dd ff ff       	call   2310 <__stack_chk_fail@plt>
    45ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000045f0 <add_accept_request>:
    45f0:	f3 0f 1e fa          	endbr64
    45f4:	55                   	push   %rbp
    45f5:	53                   	push   %rbx
    45f6:	48 89 cb             	mov    %rcx,%rbx
    45f9:	48 83 ec 08          	sub    $0x8,%rsp
    45fd:	8b 41 44             	mov    0x44(%rcx),%eax
    4600:	4c 8b 03             	mov    (%rbx),%r8
    4603:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
    4609:	83 c0 01             	add    $0x1,%eax
    460c:	45 8b 08             	mov    (%r8),%r9d
    460f:	f6 c1 02             	test   $0x2,%cl
    4612:	74 00                	je     4614 <add_accept_request+0x24>
    4614:	41 89 c0             	mov    %eax,%r8d
    4617:	45 29 c8             	sub    %r9d,%r8d
    461a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    461e:	0f 82 26 df ff ff    	jb     254a <add_accept_request.cold>
    4624:	c1 e9 0a             	shr    $0xa,%ecx
    4627:	8b 6b 44             	mov    0x44(%rbx),%ebp
    462a:	23 6b 58             	and    0x58(%rbx),%ebp
    462d:	89 43 44             	mov    %eax,0x44(%rbx)
    4630:	83 e1 01             	and    $0x1,%ecx
    4633:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4637:	d3 e5                	shl    %cl,%ebp
    4639:	48 c1 e5 06          	shl    $0x6,%rbp
    463d:	48 03 6b 38          	add    0x38(%rbx),%rbp
    4641:	89 7d 04             	mov    %edi,0x4(%rbp)
    4644:	bf 10 00 00 00       	mov    $0x10,%edi
    4649:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
    4650:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    4654:	48 89 75 10          	mov    %rsi,0x10(%rbp)
    4658:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    4660:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
    4668:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    466c:	e8 7f dd ff ff       	call   23f0 <malloc@plt>
    4671:	48 89 df             	mov    %rbx,%rdi
    4674:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    467a:	48 89 45 20          	mov    %rax,0x20(%rbp)
    467e:	48 83 c4 08          	add    $0x8,%rsp
    4682:	5b                   	pop    %rbx
    4683:	5d                   	pop    %rbp
    4684:	e9 97 dc ff ff       	jmp    2320 <io_uring_submit@plt>
    4689:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004690 <io_thread>:
    4690:	f3 0f 1e fa          	endbr64
    4694:	41 57                	push   %r15
    4696:	31 d2                	xor    %edx,%edx
    4698:	41 56                	push   %r14
    469a:	41 55                	push   %r13
    469c:	41 54                	push   %r12
    469e:	55                   	push   %rbp
    469f:	48 89 fd             	mov    %rdi,%rbp
    46a2:	53                   	push   %rbx
    46a3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    46aa:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    46b3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    46bb:	48 8b 47 40          	mov    0x40(%rdi),%rax
    46bf:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    46c4:	bf 00 01 00 00       	mov    $0x100,%edi
    46c9:	48 89 de             	mov    %rbx,%rsi
    46cc:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    46d0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    46d5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    46da:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    46df:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    46e4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    46ec:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    46f1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    46f9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    46fe:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    4706:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    470b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    4713:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    4718:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    4720:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    4725:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    472d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    4735:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    473d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    4745:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    474d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    4755:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    475d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    4765:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    476d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    4775:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    477d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    4784:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
    478c:	e8 3f dc ff ff       	call   23d0 <io_uring_queue_init@plt>
    4791:	48 8b 7d 40          	mov    0x40(%rbp),%rdi
    4795:	31 f6                	xor    %esi,%esi
    4797:	e8 24 dd ff ff       	call   24c0 <io_uring_register_eventfd@plt>
    479c:	31 d2                	xor    %edx,%edx
    479e:	be 01 00 00 00       	mov    $0x1,%esi
    47a3:	bf 02 00 00 00       	mov    $0x2,%edi
    47a8:	e8 63 dd ff ff       	call   2510 <socket@plt>
    47ad:	83 f8 ff             	cmp    $0xffffffff,%eax
    47b0:	0f 84 08 06 00 00    	je     4dbe <io_thread+0x72e>
    47b6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    47bb:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    47c1:	89 c7                	mov    %eax,%edi
    47c3:	41 89 c4             	mov    %eax,%r12d
    47c6:	ba 02 00 00 00       	mov    $0x2,%edx
    47cb:	be 01 00 00 00       	mov    $0x1,%esi
    47d0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    47d8:	e8 03 db ff ff       	call   22e0 <setsockopt@plt>
    47dd:	85 c0                	test   %eax,%eax
    47df:	0f 88 cd 05 00 00    	js     4db2 <io_thread+0x722>
    47e5:	8b 05 85 20 00 00    	mov    0x2085(%rip),%eax        # 6870 <_IO_stdin_used+0x870>
    47eb:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    47f0:	ba 10 00 00 00       	mov    $0x10,%edx
    47f5:	44 89 e7             	mov    %r12d,%edi
    47f8:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    4801:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    4809:	89 44 24 40          	mov    %eax,0x40(%rsp)
    480d:	e8 2e dc ff ff       	call   2440 <bind@plt>
    4812:	85 c0                	test   %eax,%eax
    4814:	0f 88 8c 05 00 00    	js     4da6 <io_thread+0x716>
    481a:	be 0a 00 00 00       	mov    $0xa,%esi
    481f:	44 89 e7             	mov    %r12d,%edi
    4822:	e8 d9 db ff ff       	call   2400 <listen@plt>
    4827:	85 c0                	test   %eax,%eax
    4829:	0f 88 6b 05 00 00    	js     4d9a <io_thread+0x70a>
    482f:	ba 50 00 00 00       	mov    $0x50,%edx
    4834:	48 8d 35 41 19 00 00 	lea    0x1941(%rip),%rsi        # 617c <_IO_stdin_used+0x17c>
    483b:	bf 01 00 00 00       	mov    $0x1,%edi
    4840:	31 c0                	xor    %eax,%eax
    4842:	e8 e9 db ff ff       	call   2430 <__printf_chk@plt>
    4847:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    484c:	48 89 d9             	mov    %rbx,%rcx
    484f:	44 89 e7             	mov    %r12d,%edi
    4852:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    4857:	48 89 c6             	mov    %rax,%rsi
    485a:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    485f:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
    4864:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
    486c:	e8 7f fd ff ff       	call   45f0 <add_accept_request>
    4871:	bf 01 00 00 00       	mov    $0x1,%edi
    4876:	be 10 00 00 00       	mov    $0x10,%esi
    487b:	e8 00 db ff ff       	call   2380 <calloc@plt>
    4880:	bf 0a 00 00 00       	mov    $0xa,%edi
    4885:	49 89 c5             	mov    %rax,%r13
    4888:	e8 63 db ff ff       	call   23f0 <malloc@plt>
    488d:	48 85 c0             	test   %rax,%rax
    4890:	0f 84 dd 04 00 00    	je     4d73 <io_thread+0x6e3>
    4896:	49 89 45 00          	mov    %rax,0x0(%r13)
    489a:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    48a1:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    48a8:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
    48b0:	8d 50 01             	lea    0x1(%rax),%edx
    48b3:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    48b8:	8b 30                	mov    (%rax),%esi
    48ba:	f6 c1 02             	test   $0x2,%cl
    48bd:	0f 85 2d 04 00 00    	jne    4cf0 <io_thread+0x660>
    48c3:	89 d0                	mov    %edx,%eax
    48c5:	29 f0                	sub    %esi,%eax
    48c7:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    48ce:	0f 82 80 dc ff ff    	jb     2554 <io_thread.cold>
    48d4:	c1 e9 0a             	shr    $0xa,%ecx
    48d7:	48 8d 75 48          	lea    0x48(%rbp),%rsi
    48db:	66 0f ef c0          	pxor   %xmm0,%xmm0
    48df:	48 89 df             	mov    %rbx,%rdi
    48e2:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    48e9:	83 e1 01             	and    $0x1,%ecx
    48ec:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    48f3:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    48fa:	d3 e0                	shl    %cl,%eax
    48fc:	8b 55 48             	mov    0x48(%rbp),%edx
    48ff:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    4904:	48 c1 e0 06          	shl    $0x6,%rax
    4908:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    4910:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    4916:	89 50 04             	mov    %edx,0x4(%rax)
    4919:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4921:	4c 89 68 10          	mov    %r13,0x10(%rax)
    4925:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    492d:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4935:	48 89 70 20          	mov    %rsi,0x20(%rax)
    4939:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    493d:	e8 de d9 ff ff       	call   2320 <io_uring_submit@plt>
    4942:	8b 45 2c             	mov    0x2c(%rbp),%eax
    4945:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    494a:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    4952:	83 f8 01             	cmp    $0x1,%eax
    4955:	0f 85 b8 01 00 00    	jne    4b13 <io_thread+0x483>
    495b:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    4960:	4d 89 ce             	mov    %r9,%r14
    4963:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    4968:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4970:	48 8d 3d 1b 18 00 00 	lea    0x181b(%rip),%rdi        # 6192 <_IO_stdin_used+0x192>
    4977:	e8 54 d9 ff ff       	call   22d0 <puts@plt>
    497c:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4983:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
    498a:	c1 e9 0b             	shr    $0xb,%ecx
    498d:	83 e1 01             	and    $0x1,%ecx
    4990:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    4998:	8b 00                	mov    (%rax),%eax
    499a:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    49a2:	8b 16                	mov    (%rsi),%edx
    49a4:	39 d0                	cmp    %edx,%eax
    49a6:	74 36                	je     49de <io_thread+0x34e>
    49a8:	89 f8                	mov    %edi,%eax
    49aa:	21 d0                	and    %edx,%eax
    49ac:	d3 e0                	shl    %cl,%eax
    49ae:	48 c1 e0 04          	shl    $0x4,%rax
    49b2:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
    49ba:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    49c2:	0f 85 88 01 00 00    	jne    4b50 <io_thread+0x4c0>
    49c8:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    49cc:	0f 85 26 03 00 00    	jne    4cf8 <io_thread+0x668>
    49d2:	8b 40 08             	mov    0x8(%rax),%eax
    49d5:	83 c2 01             	add    $0x1,%edx
    49d8:	89 16                	mov    %edx,(%rsi)
    49da:	85 c0                	test   %eax,%eax
    49dc:	79 b2                	jns    4990 <io_thread+0x300>
    49de:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    49e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    49f0:	45 31 c0             	xor    %r8d,%r8d
    49f3:	31 d2                	xor    %edx,%edx
    49f5:	b9 01 00 00 00       	mov    $0x1,%ecx
    49fa:	4c 89 f6             	mov    %r14,%rsi
    49fd:	48 89 df             	mov    %rbx,%rdi
    4a00:	e8 1b da ff ff       	call   2420 <__io_uring_get_cqe@plt>
    4a05:	41 89 c7             	mov    %eax,%r15d
    4a08:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4a0d:	48 83 38 01          	cmpq   $0x1,(%rax)
    4a11:	0f 84 f1 02 00 00    	je     4d08 <io_thread+0x678>
    4a17:	48 8d 3d 9a 17 00 00 	lea    0x179a(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4a1e:	e8 ad d8 ff ff       	call   22d0 <puts@plt>
    4a23:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4a28:	4c 8b 22             	mov    (%rdx),%r12
    4a2b:	45 85 ff             	test   %r15d,%r15d
    4a2e:	0f 88 2e 03 00 00    	js     4d62 <io_thread+0x6d2>
    4a34:	8b 42 08             	mov    0x8(%rdx),%eax
    4a37:	45 8b 04 24          	mov    (%r12),%r8d
    4a3b:	85 c0                	test   %eax,%eax
    4a3d:	0f 88 e5 02 00 00    	js     4d28 <io_thread+0x698>
    4a43:	41 83 f8 01          	cmp    $0x1,%r8d
    4a47:	0f 84 3b 01 00 00    	je     4b88 <io_thread+0x4f8>
    4a4d:	41 83 f8 02          	cmp    $0x2,%r8d
    4a51:	0f 84 b1 01 00 00    	je     4c08 <io_thread+0x578>
    4a57:	45 85 c0             	test   %r8d,%r8d
    4a5a:	0f 84 70 01 00 00    	je     4bd0 <io_thread+0x540>
    4a60:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    4a68:	8b 02                	mov    (%rdx),%eax
    4a6a:	83 c0 01             	add    $0x1,%eax
    4a6d:	89 02                	mov    %eax,(%rdx)
    4a6f:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4a76:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    4a7d:	8d 50 01             	lea    0x1(%rax),%edx
    4a80:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    4a85:	8b 30                	mov    (%rax),%esi
    4a87:	f6 c1 02             	test   $0x2,%cl
    4a8a:	74 00                	je     4a8c <io_thread+0x3fc>
    4a8c:	89 d0                	mov    %edx,%eax
    4a8e:	29 f0                	sub    %esi,%eax
    4a90:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    4a97:	0f 82 b7 da ff ff    	jb     2554 <io_thread.cold>
    4a9d:	c1 e9 0a             	shr    $0xa,%ecx
    4aa0:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    4aa5:	66 0f ef c0          	pxor   %xmm0,%xmm0
    4aa9:	48 89 df             	mov    %rbx,%rdi
    4aac:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    4ab3:	83 e1 01             	and    $0x1,%ecx
    4ab6:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    4abd:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    4ac4:	d3 e0                	shl    %cl,%eax
    4ac6:	8b 55 48             	mov    0x48(%rbp),%edx
    4ac9:	48 c1 e0 06          	shl    $0x6,%rax
    4acd:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    4ad5:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    4adb:	89 50 04             	mov    %edx,0x4(%rax)
    4ade:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    4ae6:	4c 89 68 10          	mov    %r13,0x10(%rax)
    4aea:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    4af2:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    4afa:	48 89 70 20          	mov    %rsi,0x20(%rax)
    4afe:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    4b02:	e8 19 d8 ff ff       	call   2320 <io_uring_submit@plt>
    4b07:	8b 45 2c             	mov    0x2c(%rbp),%eax
    4b0a:	83 f8 01             	cmp    $0x1,%eax
    4b0d:	0f 84 5d fe ff ff    	je     4970 <io_thread+0x2e0>
    4b13:	48 8d 3d d7 16 00 00 	lea    0x16d7(%rip),%rdi        # 61f1 <_IO_stdin_used+0x1f1>
    4b1a:	e8 b1 d7 ff ff       	call   22d0 <puts@plt>
    4b1f:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    4b27:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4b30:	0f 85 38 02 00 00    	jne    4d6e <io_thread+0x6de>
    4b36:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    4b3d:	31 c0                	xor    %eax,%eax
    4b3f:	5b                   	pop    %rbx
    4b40:	5d                   	pop    %rbp
    4b41:	41 5c                	pop    %r12
    4b43:	41 5d                	pop    %r13
    4b45:	41 5e                	pop    %r14
    4b47:	41 5f                	pop    %r15
    4b49:	c3                   	ret
    4b4a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4b50:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    4b55:	48 85 c0             	test   %rax,%rax
    4b58:	0f 84 92 fe ff ff    	je     49f0 <io_thread+0x360>
    4b5e:	48 83 38 01          	cmpq   $0x1,(%rax)
    4b62:	0f 84 a0 01 00 00    	je     4d08 <io_thread+0x678>
    4b68:	48 8d 3d 49 16 00 00 	lea    0x1649(%rip),%rdi        # 61b8 <_IO_stdin_used+0x1b8>
    4b6f:	e8 5c d7 ff ff       	call   22d0 <puts@plt>
    4b74:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4b79:	4c 8b 22             	mov    (%rdx),%r12
    4b7c:	e9 b3 fe ff ff       	jmp    4a34 <io_thread+0x3a4>
    4b81:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4b88:	85 c0                	test   %eax,%eax
    4b8a:	0f 85 c0 00 00 00    	jne    4c50 <io_thread+0x5c0>
    4b90:	48 8b 0d 89 44 00 00 	mov    0x4489(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4b97:	ba 0f 00 00 00       	mov    $0xf,%edx
    4b9c:	be 01 00 00 00       	mov    $0x1,%esi
    4ba1:	48 8d 3d 39 16 00 00 	lea    0x1639(%rip),%rdi        # 61e1 <_IO_stdin_used+0x1e1>
    4ba8:	e8 f3 d8 ff ff       	call   24a0 <fwrite@plt>
    4bad:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4bb2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4bb8:	48 85 c0             	test   %rax,%rax
    4bbb:	0f 84 ae fe ff ff    	je     4a6f <io_thread+0x3df>
    4bc1:	e9 9a fe ff ff       	jmp    4a60 <io_thread+0x3d0>
    4bc6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4bd0:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    4bd5:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    4bda:	48 89 d9             	mov    %rbx,%rcx
    4bdd:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    4be1:	e8 0a fa ff ff       	call   45f0 <add_accept_request>
    4be6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4beb:	48 89 de             	mov    %rbx,%rsi
    4bee:	8b 78 08             	mov    0x8(%rax),%edi
    4bf1:	e8 9a f3 ff ff       	call   3f90 <add_read_request>
    4bf6:	4c 89 e7             	mov    %r12,%rdi
    4bf9:	e8 b2 d6 ff ff       	call   22b0 <free@plt>
    4bfe:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4c03:	eb b3                	jmp    4bb8 <io_thread+0x528>
    4c05:	0f 1f 00             	nopl   (%rax)
    4c08:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    4c0d:	45 31 ff             	xor    %r15d,%r15d
    4c10:	85 c0                	test   %eax,%eax
    4c12:	7e 20                	jle    4c34 <io_thread+0x5a4>
    4c14:	0f 1f 40 00          	nopl   0x0(%rax)
    4c18:	4c 89 f8             	mov    %r15,%rax
    4c1b:	49 83 c7 01          	add    $0x1,%r15
    4c1f:	48 c1 e0 04          	shl    $0x4,%rax
    4c23:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    4c28:	e8 83 d6 ff ff       	call   22b0 <free@plt>
    4c2d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    4c32:	7f e4                	jg     4c18 <io_thread+0x588>
    4c34:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    4c39:	e8 12 d7 ff ff       	call   2350 <close@plt>
    4c3e:	4c 89 e7             	mov    %r12,%rdi
    4c41:	e8 6a d6 ff ff       	call   22b0 <free@plt>
    4c46:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4c4b:	e9 68 ff ff ff       	jmp    4bb8 <io_thread+0x528>
    4c50:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    4c55:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4c5a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    4c62:	eb 11                	jmp    4c75 <io_thread+0x5e5>
    4c64:	0f 1f 40 00          	nopl   0x0(%rax)
    4c68:	48 83 c0 01          	add    $0x1,%rax
    4c6c:	48 83 c2 01          	add    $0x1,%rdx
    4c70:	48 39 c6             	cmp    %rax,%rsi
    4c73:	74 4b                	je     4cc0 <io_thread+0x630>
    4c75:	0f b6 0a             	movzbl (%rdx),%ecx
    4c78:	88 08                	mov    %cl,(%rax)
    4c7a:	80 f9 0d             	cmp    $0xd,%cl
    4c7d:	75 e9                	jne    4c68 <io_thread+0x5d8>
    4c7f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    4c83:	75 e3                	jne    4c68 <io_thread+0x5d8>
    4c85:	c6 00 00             	movb   $0x0,(%rax)
    4c88:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    4c8d:	48 89 da             	mov    %rbx,%rdx
    4c90:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    4c95:	e8 76 f7 ff ff       	call   4410 <handle_http_method>
    4c9a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    4c9f:	e8 0c d6 ff ff       	call   22b0 <free@plt>
    4ca4:	4c 89 e7             	mov    %r12,%rdi
    4ca7:	e8 04 d6 ff ff       	call   22b0 <free@plt>
    4cac:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4cb1:	e9 02 ff ff ff       	jmp    4bb8 <io_thread+0x528>
    4cb6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4cc0:	48 8b 0d 59 43 00 00 	mov    0x4359(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4cc7:	ba 12 00 00 00       	mov    $0x12,%edx
    4ccc:	be 01 00 00 00       	mov    $0x1,%esi
    4cd1:	48 8d 3d 5f 14 00 00 	lea    0x145f(%rip),%rdi        # 6137 <_IO_stdin_used+0x137>
    4cd8:	e8 c3 d7 ff ff       	call   24a0 <fwrite@plt>
    4cdd:	bf 01 00 00 00       	mov    $0x1,%edi
    4ce2:	e8 99 d7 ff ff       	call   2480 <exit@plt>
    4ce7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4cf0:	e9 ce fb ff ff       	jmp    48c3 <io_thread+0x233>
    4cf5:	0f 1f 00             	nopl   (%rax)
    4cf8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    4cfd:	e9 5c fe ff ff       	jmp    4b5e <io_thread+0x4ce>
    4d02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4d08:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    4d10:	48 8d 3d 8d 14 00 00 	lea    0x148d(%rip),%rdi        # 61a4 <_IO_stdin_used+0x1a4>
    4d17:	8b 02                	mov    (%rdx),%eax
    4d19:	83 c0 01             	add    $0x1,%eax
    4d1c:	89 02                	mov    %eax,(%rdx)
    4d1e:	e8 ad d5 ff ff       	call   22d0 <puts@plt>
    4d23:	e9 eb fd ff ff       	jmp    4b13 <io_thread+0x483>
    4d28:	f7 d8                	neg    %eax
    4d2a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    4d2f:	89 c7                	mov    %eax,%edi
    4d31:	e8 aa d7 ff ff       	call   24e0 <strerror@plt>
    4d36:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    4d3b:	be 01 00 00 00       	mov    $0x1,%esi
    4d40:	48 8b 3d d9 42 00 00 	mov    0x42d9(%rip),%rdi        # 9020 <stderr@GLIBC_2.2.5>
    4d47:	48 89 c1             	mov    %rax,%rcx
    4d4a:	48 8d 15 27 16 00 00 	lea    0x1627(%rip),%rdx        # 6378 <_IO_stdin_used+0x378>
    4d51:	31 c0                	xor    %eax,%eax
    4d53:	e8 58 d7 ff ff       	call   24b0 <__fprintf_chk@plt>
    4d58:	bf 01 00 00 00       	mov    $0x1,%edi
    4d5d:	e8 1e d7 ff ff       	call   2480 <exit@plt>
    4d62:	48 8d 3d 66 14 00 00 	lea    0x1466(%rip),%rdi        # 61cf <_IO_stdin_used+0x1cf>
    4d69:	e8 a2 ea ff ff       	call   3810 <fatal_error>
    4d6e:	e8 9d d5 ff ff       	call   2310 <__stack_chk_fail@plt>
    4d73:	48 8b 0d a6 42 00 00 	mov    0x42a6(%rip),%rcx        # 9020 <stderr@GLIBC_2.2.5>
    4d7a:	ba 28 00 00 00       	mov    $0x28,%edx
    4d7f:	be 01 00 00 00       	mov    $0x1,%esi
    4d84:	48 8d 3d bd 15 00 00 	lea    0x15bd(%rip),%rdi        # 6348 <_IO_stdin_used+0x348>
    4d8b:	e8 10 d7 ff ff       	call   24a0 <fwrite@plt>
    4d90:	bf 01 00 00 00       	mov    $0x1,%edi
    4d95:	e8 e6 d6 ff ff       	call   2480 <exit@plt>
    4d9a:	48 8d 3d d2 13 00 00 	lea    0x13d2(%rip),%rdi        # 6173 <_IO_stdin_used+0x173>
    4da1:	e8 6a ea ff ff       	call   3810 <fatal_error>
    4da6:	48 8d 3d bf 13 00 00 	lea    0x13bf(%rip),%rdi        # 616c <_IO_stdin_used+0x16c>
    4dad:	e8 5e ea ff ff       	call   3810 <fatal_error>
    4db2:	48 8d 3d 9a 13 00 00 	lea    0x139a(%rip),%rdi        # 6153 <_IO_stdin_used+0x153>
    4db9:	e8 52 ea ff ff       	call   3810 <fatal_error>
    4dbe:	48 8d 3d 85 13 00 00 	lea    0x1385(%rip),%rdi        # 614a <_IO_stdin_used+0x14a>
    4dc5:	e8 46 ea ff ff       	call   3810 <fatal_error>
    4dca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004dd0 <receive>:
    4dd0:	f3 0f 1e fa          	endbr64
    4dd4:	8b 57 3c             	mov    0x3c(%rdi),%edx
    4dd7:	85 d2                	test   %edx,%edx
    4dd9:	0f 8e d1 00 00 00    	jle    4eb0 <receive+0xe0>
    4ddf:	48 89 f8             	mov    %rdi,%rax
    4de2:	45 31 db             	xor    %r11d,%r11d
    4de5:	0f 1f 00             	nopl   (%rax)
    4de8:	48 8b 50 70          	mov    0x70(%rax),%rdx
    4dec:	4c 89 df             	mov    %r11,%rdi
    4def:	48 c1 e7 05          	shl    $0x5,%rdi
    4df3:	4c 8b 0c 3a          	mov    (%rdx,%rdi,1),%r9
    4df7:	49 8b 51 08          	mov    0x8(%r9),%rdx
    4dfb:	48 85 d2             	test   %rdx,%rdx
    4dfe:	0f 8e 94 00 00 00    	jle    4e98 <receive+0xc8>
    4e04:	4d 8b 11             	mov    (%r9),%r10
    4e07:	31 d2                	xor    %edx,%edx
    4e09:	eb 12                	jmp    4e1d <receive+0x4d>
    4e0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4e10:	49 8b 49 08          	mov    0x8(%r9),%rcx
    4e14:	48 83 c2 01          	add    $0x1,%rdx
    4e18:	48 39 d1             	cmp    %rdx,%rcx
    4e1b:	7e 7b                	jle    4e98 <receive+0xc8>
    4e1d:	48 8b 48 78          	mov    0x78(%rax),%rcx
    4e21:	49 8b 34 d2          	mov    (%r10,%rdx,8),%rsi
    4e25:	48 83 c1 01          	add    $0x1,%rcx
    4e29:	4c 8b 46 10          	mov    0x10(%rsi),%r8
    4e2d:	48 89 48 78          	mov    %rcx,0x78(%rax)
    4e31:	48 8b 48 10          	mov    0x10(%rax),%rcx
    4e35:	48 83 c1 01          	add    $0x1,%rcx
    4e39:	48 89 48 10          	mov    %rcx,0x10(%rax)
    4e3d:	48 8b 48 70          	mov    0x70(%rax),%rcx
    4e41:	48 83 44 39 18 01    	addq   $0x1,0x18(%rcx,%rdi,1)
    4e47:	48 63 08             	movslq (%rax),%rcx
    4e4a:	49 39 c8             	cmp    %rcx,%r8
    4e4d:	75 c1                	jne    4e10 <receive+0x40>
    4e4f:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    4e53:	48 63 48 38          	movslq 0x38(%rax),%rcx
    4e57:	48 39 ce             	cmp    %rcx,%rsi
    4e5a:	75 b4                	jne    4e10 <receive+0x40>
    4e5c:	48 83 ec 08          	sub    $0x8,%rsp
    4e60:	48 63 50 38          	movslq 0x38(%rax),%rdx
    4e64:	48 63 00             	movslq (%rax),%rax
    4e67:	31 c9                	xor    %ecx,%ecx
    4e69:	bf 01 00 00 00       	mov    $0x1,%edi
    4e6e:	48 39 f2             	cmp    %rsi,%rdx
    4e71:	48 8d 35 28 15 00 00 	lea    0x1528(%rip),%rsi        # 63a0 <_IO_stdin_used+0x3a0>
    4e78:	0f 94 c1             	sete   %cl
    4e7b:	31 d2                	xor    %edx,%edx
    4e7d:	4c 39 c0             	cmp    %r8,%rax
    4e80:	0f 94 c2             	sete   %dl
    4e83:	31 c0                	xor    %eax,%eax
    4e85:	e8 a6 d5 ff ff       	call   2430 <__printf_chk@plt>
    4e8a:	bf 01 00 00 00       	mov    $0x1,%edi
    4e8f:	e8 ec d5 ff ff       	call   2480 <exit@plt>
    4e94:	0f 1f 40 00          	nopl   0x0(%rax)
    4e98:	49 c7 41 08 00 00 00 00 	movq   $0x0,0x8(%r9)
    4ea0:	8b 50 3c             	mov    0x3c(%rax),%edx
    4ea3:	49 83 c3 01          	add    $0x1,%r11
    4ea7:	44 39 da             	cmp    %r11d,%edx
    4eaa:	0f 8f 38 ff ff ff    	jg     4de8 <receive+0x18>
    4eb0:	c3                   	ret
    4eb1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4ebc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004ec0 <barriered_work>:
    4ec0:	f3 0f 1e fa          	endbr64
    4ec4:	41 55                	push   %r13
    4ec6:	41 54                	push   %r12
    4ec8:	55                   	push   %rbp
    4ec9:	53                   	push   %rbx
    4eca:	48 89 fb             	mov    %rdi,%rbx
    4ecd:	48 83 ec 08          	sub    $0x8,%rsp
    4ed1:	8b 57 38             	mov    0x38(%rdi),%edx
    4ed4:	8b 07                	mov    (%rdi),%eax
    4ed6:	39 c2                	cmp    %eax,%edx
    4ed8:	0f 84 d2 00 00 00    	je     4fb0 <barriered_work+0xf0>
    4ede:	e8 ed fe ff ff       	call   4dd0 <receive>
    4ee3:	8b 43 48             	mov    0x48(%rbx),%eax
    4ee6:	83 f8 01             	cmp    $0x1,%eax
    4ee9:	75 19                	jne    4f04 <barriered_work+0x44>
    4eeb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4ef0:	48 8b 43 10          	mov    0x10(%rbx),%rax
    4ef4:	48 83 c0 01          	add    $0x1,%rax
    4ef8:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4efc:	8b 43 48             	mov    0x48(%rbx),%eax
    4eff:	83 f8 01             	cmp    $0x1,%eax
    4f02:	74 ec                	je     4ef0 <barriered_work+0x30>
    4f04:	8b 83 80 00 00 00    	mov    0x80(%rbx),%eax
    4f0a:	83 f8 01             	cmp    $0x1,%eax
    4f0d:	74 10                	je     4f1f <barriered_work+0x5f>
    4f0f:	0f ae f0             	mfence
    4f12:	48 83 c4 08          	add    $0x8,%rsp
    4f16:	31 c0                	xor    %eax,%eax
    4f18:	5b                   	pop    %rbx
    4f19:	5d                   	pop    %rbp
    4f1a:	41 5c                	pop    %r12
    4f1c:	41 5d                	pop    %r13
    4f1e:	c3                   	ret
    4f1f:	8b 43 3c             	mov    0x3c(%rbx),%eax
    4f22:	85 c0                	test   %eax,%eax
    4f24:	7e e9                	jle    4f0f <barriered_work+0x4f>
    4f26:	45 31 c9             	xor    %r9d,%r9d
    4f29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4f30:	8b 43 38             	mov    0x38(%rbx),%eax
    4f33:	44 39 c8             	cmp    %r9d,%eax
    4f36:	74 5e                	je     4f96 <barriered_work+0xd6>
    4f38:	48 8b 43 70          	mov    0x70(%rbx),%rax
    4f3c:	4c 89 c9             	mov    %r9,%rcx
    4f3f:	48 c1 e1 05          	shl    $0x5,%rcx
    4f43:	48 8b 54 08 08       	mov    0x8(%rax,%rcx,1),%rdx
    4f48:	48 8b 42 08          	mov    0x8(%rdx),%rax
    4f4c:	48 63 7a 10          	movslq 0x10(%rdx),%rdi
    4f50:	48 39 f8             	cmp    %rdi,%rax
    4f53:	7d 41                	jge    4f96 <barriered_work+0xd6>
    4f55:	4c 8b 02             	mov    (%rdx),%r8
    4f58:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4f60:	48 8b 43 10          	mov    0x10(%rbx),%rax
    4f64:	48 83 c0 01          	add    $0x1,%rax
    4f68:	48 89 43 10          	mov    %rax,0x10(%rbx)
    4f6c:	48 8b 43 70          	mov    0x70(%rbx),%rax
    4f70:	48 83 44 08 10 01    	addq   $0x1,0x10(%rax,%rcx,1)
    4f76:	48 8b 42 08          	mov    0x8(%rdx),%rax
    4f7a:	48 8d 70 01          	lea    0x1(%rax),%rsi
    4f7e:	48 89 72 08          	mov    %rsi,0x8(%rdx)
    4f82:	48 8b b3 88 00 00 00 	mov    0x88(%rbx),%rsi
    4f89:	49 89 34 c0          	mov    %rsi,(%r8,%rax,8)
    4f8d:	48 8b 42 08          	mov    0x8(%rdx),%rax
    4f91:	48 39 f8             	cmp    %rdi,%rax
    4f94:	7c ca                	jl     4f60 <barriered_work+0xa0>
    4f96:	8b 43 3c             	mov    0x3c(%rbx),%eax
    4f99:	49 83 c1 01          	add    $0x1,%r9
    4f9d:	44 39 c8             	cmp    %r9d,%eax
    4fa0:	7f 8e                	jg     4f30 <barriered_work+0x70>
    4fa2:	e9 68 ff ff ff       	jmp    4f0f <barriered_work+0x4f>
    4fa7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4fb0:	e8 1b fe ff ff       	call   4dd0 <receive>
    4fb5:	8b 3b                	mov    (%rbx),%edi
    4fb7:	8b 43 3c             	mov    0x3c(%rbx),%eax
    4fba:	85 c0                	test   %eax,%eax
    4fbc:	0f 8e ae 00 00 00    	jle    5070 <barriered_work+0x1b0>
    4fc2:	48 63 c7             	movslq %edi,%rax
    4fc5:	45 31 d2             	xor    %r10d,%r10d
    4fc8:	45 31 e4             	xor    %r12d,%r12d
    4fcb:	83 c7 01             	add    $0x1,%edi
    4fce:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    4fd2:	48 8d 2c 50          	lea    (%rax,%rdx,2),%rbp
    4fd6:	48 c1 e5 03          	shl    $0x3,%rbp
    4fda:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4fe0:	8b 43 3c             	mov    0x3c(%rbx),%eax
    4fe3:	4d 89 e3             	mov    %r12,%r11
    4fe6:	31 f6                	xor    %esi,%esi
    4fe8:	31 c9                	xor    %ecx,%ecx
    4fea:	49 c1 e3 05          	shl    $0x5,%r11
    4fee:	85 c0                	test   %eax,%eax
    4ff0:	7e 6a                	jle    505c <barriered_work+0x19c>
    4ff2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4ff8:	44 8b 6b 3c          	mov    0x3c(%rbx),%r13d
    4ffc:	48 8b 43 30          	mov    0x30(%rbx),%rax
    5000:	48 8b 40 10          	mov    0x10(%rax),%rax
    5004:	4a 8b 54 10 20       	mov    0x20(%rax,%r10,1),%rdx
    5009:	48 01 ea             	add    %rbp,%rdx
    500c:	4c 8b 42 70          	mov    0x70(%rdx),%r8
    5010:	48 8b 43 30          	mov    0x30(%rbx),%rax
    5014:	4c 8b 48 10          	mov    0x10(%rax),%r9
    5018:	89 f8                	mov    %edi,%eax
    501a:	99                   	cltd
    501b:	41 f7 fd             	idiv   %r13d
    501e:	89 d0                	mov    %edx,%eax
    5020:	f7 d8                	neg    %eax
    5022:	0f 49 d0             	cmovns %eax,%edx
    5025:	48 63 d2             	movslq %edx,%rdx
    5028:	48 8d 04 d2          	lea    (%rdx,%rdx,8),%rax
    502c:	48 8d 14 42          	lea    (%rdx,%rax,2),%rdx
    5030:	49 8b 44 31 20       	mov    0x20(%r9,%rsi,1),%rax
    5035:	48 83 c6 78          	add    $0x78,%rsi
    5039:	48 8d 04 d0          	lea    (%rax,%rdx,8),%rax
    503d:	48 89 ca             	mov    %rcx,%rdx
    5040:	48 83 c1 01          	add    $0x1,%rcx
    5044:	48 c1 e2 05          	shl    $0x5,%rdx
    5048:	48 8b 40 70          	mov    0x70(%rax),%rax
    504c:	49 8b 54 10 08       	mov    0x8(%r8,%rdx,1),%rdx
    5051:	4a 89 14 18          	mov    %rdx,(%rax,%r11,1)
    5055:	8b 43 3c             	mov    0x3c(%rbx),%eax
    5058:	39 c8                	cmp    %ecx,%eax
    505a:	7f 9c                	jg     4ff8 <barriered_work+0x138>
    505c:	8b 43 3c             	mov    0x3c(%rbx),%eax
    505f:	49 83 c4 01          	add    $0x1,%r12
    5063:	49 83 c2 78          	add    $0x78,%r10
    5067:	44 39 e0             	cmp    %r12d,%eax
    506a:	0f 8f 70 ff ff ff    	jg     4fe0 <barriered_work+0x120>
    5070:	0f ae f0             	mfence
    5073:	48 8b 73 50          	mov    0x50(%rbx),%rsi
    5077:	48 8b 43 60          	mov    0x60(%rbx),%rax
    507b:	31 ff                	xor    %edi,%edi
    507d:	48 c1 e0 05          	shl    $0x5,%rax
    5081:	48 01 c6             	add    %rax,%rsi
    5084:	e8 67 d2 ff ff       	call   22f0 <clock_gettime@plt>
    5089:	48 8b 43 30          	mov    0x30(%rbx),%rax
    508d:	48 8b 40 30          	mov    0x30(%rax),%rax
    5091:	8b 78 10             	mov    0x10(%rax),%edi
    5094:	8d 6f 01             	lea    0x1(%rdi),%ebp
    5097:	89 68 10             	mov    %ebp,0x10(%rax)
    509a:	8b 43 48             	mov    0x48(%rbx),%eax
    509d:	83 f8 01             	cmp    $0x1,%eax
    50a0:	75 4d                	jne    50ef <barriered_work+0x22f>
    50a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    50a8:	48 8b 43 10          	mov    0x10(%rbx),%rax
    50ac:	48 83 c0 01          	add    $0x1,%rax
    50b0:	48 89 43 10          	mov    %rax,0x10(%rbx)
    50b4:	48 8b 73 28          	mov    0x28(%rbx),%rsi
    50b8:	48 8b 7b 30          	mov    0x30(%rbx),%rdi
    50bc:	48 63 4b 38          	movslq 0x38(%rbx),%rcx
    50c0:	48 63 13             	movslq (%rbx),%rdx
    50c3:	48 89 c8             	mov    %rcx,%rax
    50c6:	48 c1 e0 04          	shl    $0x4,%rax
    50ca:	48 29 c8             	sub    %rcx,%rax
    50cd:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    50d1:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    50d5:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    50d9:	48 8b 40 20          	mov    0x20(%rax),%rax
    50dd:	48 8d 14 4a          	lea    (%rdx,%rcx,2),%rdx
    50e1:	48 8d 3c d0          	lea    (%rax,%rdx,8),%rdi
    50e5:	ff d6                	call   *%rsi
    50e7:	8b 43 48             	mov    0x48(%rbx),%eax
    50ea:	83 f8 01             	cmp    $0x1,%eax
    50ed:	74 b9                	je     50a8 <barriered_work+0x1e8>
    50ef:	48 8b 43 30          	mov    0x30(%rbx),%rax
    50f3:	48 8b 40 30          	mov    0x30(%rax),%rax
    50f7:	3b 68 10             	cmp    0x10(%rax),%ebp
    50fa:	75 32                	jne    512e <barriered_work+0x26e>
    50fc:	48 8b 53 50          	mov    0x50(%rbx),%rdx
    5100:	48 8b 43 60          	mov    0x60(%rbx),%rax
    5104:	31 ff                	xor    %edi,%edi
    5106:	48 c1 e0 05          	shl    $0x5,%rax
    510a:	48 8d 74 02 10       	lea    0x10(%rdx,%rax,1),%rsi
    510f:	e8 dc d1 ff ff       	call   22f0 <clock_gettime@plt>
    5114:	48 8b 43 60          	mov    0x60(%rbx),%rax
    5118:	48 8b 4b 58          	mov    0x58(%rbx),%rcx
    511c:	48 83 c0 01          	add    $0x1,%rax
    5120:	48 99                	cqto
    5122:	48 f7 f9             	idiv   %rcx
    5125:	48 89 53 60          	mov    %rdx,0x60(%rbx)
    5129:	e9 e1 fd ff ff       	jmp    4f0f <barriered_work+0x4f>
    512e:	48 8d 3d cf 10 00 00 	lea    0x10cf(%rip),%rdi        # 6204 <_IO_stdin_used+0x204>
    5135:	e8 96 d1 ff ff       	call   22d0 <puts@plt>
    513a:	eb c0                	jmp    50fc <barriered_work+0x23c>
    513c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005140 <barriered_work_ingest>:
    5140:	f3 0f 1e fa          	endbr64
    5144:	48 83 ec 08          	sub    $0x8,%rsp
    5148:	48 8b 47 30          	mov    0x30(%rdi),%rax
    514c:	48 8b 40 38          	mov    0x38(%rax),%rax
    5150:	8b 00                	mov    (%rax),%eax
    5152:	85 c0                	test   %eax,%eax
    5154:	7e 57                	jle    51ad <barriered_work_ingest+0x6d>
    5156:	31 c0                	xor    %eax,%eax
    5158:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5160:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
    5164:	48 89 c2             	mov    %rax,%rdx
    5167:	48 c1 e2 04          	shl    $0x4,%rdx
    516b:	48 8b 49 38          	mov    0x38(%rcx),%rcx
    516f:	48 8b 71 08          	mov    0x8(%rcx),%rsi
    5173:	48 01 d6             	add    %rdx,%rsi
    5176:	8b 4e 08             	mov    0x8(%rsi),%ecx
    5179:	83 f9 01             	cmp    $0x1,%ecx
    517c:	75 1f                	jne    519d <barriered_work_ingest+0x5d>
    517e:	48 8b 4f 68          	mov    0x68(%rdi),%rcx
    5182:	48 83 c1 01          	add    $0x1,%rcx
    5186:	48 89 4f 68          	mov    %rcx,0x68(%rdi)
    518a:	48 8b 4f 30          	mov    0x30(%rdi),%rcx
    518e:	48 8b 49 38          	mov    0x38(%rcx),%rcx
    5192:	48 03 51 08          	add    0x8(%rcx),%rdx
    5196:	c7 42 08 00 00 00 00 	movl   $0x0,0x8(%rdx)
    519d:	48 8b 57 30          	mov    0x30(%rdi),%rdx
    51a1:	48 83 c0 01          	add    $0x1,%rax
    51a5:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    51a9:	39 02                	cmp    %eax,(%rdx)
    51ab:	7f b3                	jg     5160 <barriered_work_ingest+0x20>
    51ad:	0f ae f0             	mfence
    51b0:	e8 0b fd ff ff       	call   4ec0 <barriered_work>
    51b5:	31 c0                	xor    %eax,%eax
    51b7:	48 83 c4 08          	add    $0x8,%rsp
    51bb:	c3                   	ret
    51bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000051c0 <barriered_nulltask>:
    51c0:	f3 0f 1e fa          	endbr64
    51c4:	31 c0                	xor    %eax,%eax
    51c6:	c3                   	ret
    51c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000051d0 <barriered_steal>:
    51d0:	f3 0f 1e fa          	endbr64
    51d4:	31 c0                	xor    %eax,%eax
    51d6:	c3                   	ret
    51d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000051e0 <after>:
    51e0:	f3 0f 1e fa          	endbr64
    51e4:	31 c0                	xor    %eax,%eax
    51e6:	48 39 d7             	cmp    %rdx,%rdi
    51e9:	7e 08                	jle    51f3 <after+0x13>
    51eb:	31 c0                	xor    %eax,%eax
    51ed:	48 39 ce             	cmp    %rcx,%rsi
    51f0:	0f 9f c0             	setg   %al
    51f3:	c3                   	ret
    51f4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    51ff:	90                   	nop

0000000000005200 <within>:
    5200:	f3 0f 1e fa          	endbr64
    5204:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    5209:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    520e:	31 c0                	xor    %eax,%eax
    5210:	48 39 d7             	cmp    %rdx,%rdi
    5213:	7f 18                	jg     522d <within+0x2d>
    5215:	4d 39 d8             	cmp    %r11,%r8
    5218:	0f 9e c2             	setle  %dl
    521b:	48 39 ce             	cmp    %rcx,%rsi
    521e:	0f 9e c0             	setle  %al
    5221:	21 c2                	and    %eax,%edx
    5223:	31 c0                	xor    %eax,%eax
    5225:	4d 39 d1             	cmp    %r10,%r9
    5228:	0f 9e c0             	setle  %al
    522b:	21 d0                	and    %edx,%eax
    522d:	c3                   	ret
    522e:	66 90                	xchg   %ax,%ax

0000000000005230 <overlap>:
    5230:	f3 0f 1e fa          	endbr64
    5234:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5239:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    523e:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    5243:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    5248:	4c 8b 4c 24 38       	mov    0x38(%rsp),%r9
    524d:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
    5252:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    5257:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    525c:	48 39 fe             	cmp    %rdi,%rsi
    525f:	7d 2f                	jge    5290 <overlap+0x60>
    5261:	48 39 ca             	cmp    %rcx,%rdx
    5264:	7d 62                	jge    52c8 <overlap+0x98>
    5266:	4d 39 da             	cmp    %r11,%r10
    5269:	7e 0e                	jle    5279 <overlap+0x49>
    526b:	b8 01 00 00 00       	mov    $0x1,%eax
    5270:	4d 39 c1             	cmp    %r8,%r9
    5273:	0f 8f 7f 00 00 00    	jg     52f8 <overlap+0xc8>
    5279:	31 c0                	xor    %eax,%eax
    527b:	4d 39 c1             	cmp    %r8,%r9
    527e:	7c 4c                	jl     52cc <overlap+0x9c>
    5280:	31 c0                	xor    %eax,%eax
    5282:	4d 39 da             	cmp    %r11,%r10
    5285:	0f 9d c0             	setge  %al
    5288:	c3                   	ret
    5289:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5290:	7e 4e                	jle    52e0 <overlap+0xb0>
    5292:	48 39 ca             	cmp    %rcx,%rdx
    5295:	7f 39                	jg     52d0 <overlap+0xa0>
    5297:	75 31                	jne    52ca <overlap+0x9a>
    5299:	4d 39 c1             	cmp    %r8,%r9
    529c:	7f 2c                	jg     52ca <overlap+0x9a>
    529e:	b8 01 00 00 00       	mov    $0x1,%eax
    52a3:	4d 39 da             	cmp    %r11,%r10
    52a6:	7e 24                	jle    52cc <overlap+0x9c>
    52a8:	48 39 ca             	cmp    %rcx,%rdx
    52ab:	0f 94 c2             	sete   %dl
    52ae:	48 39 fe             	cmp    %rdi,%rsi
    52b1:	0f 94 c0             	sete   %al
    52b4:	21 c2                	and    %eax,%edx
    52b6:	31 c0                	xor    %eax,%eax
    52b8:	4d 39 c1             	cmp    %r8,%r9
    52bb:	0f 94 c0             	sete   %al
    52be:	21 d0                	and    %edx,%eax
    52c0:	c3                   	ret
    52c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    52c8:	74 af                	je     5279 <overlap+0x49>
    52ca:	31 c0                	xor    %eax,%eax
    52cc:	c3                   	ret
    52cd:	0f 1f 00             	nopl   (%rax)
    52d0:	4d 39 c1             	cmp    %r8,%r9
    52d3:	7d c4                	jge    5299 <overlap+0x69>
    52d5:	b8 01 00 00 00       	mov    $0x1,%eax
    52da:	4d 39 da             	cmp    %r11,%r10
    52dd:	7d ba                	jge    5299 <overlap+0x69>
    52df:	c3                   	ret
    52e0:	48 39 ca             	cmp    %rcx,%rdx
    52e3:	7c 94                	jl     5279 <overlap+0x49>
    52e5:	4d 39 c1             	cmp    %r8,%r9
    52e8:	7e b4                	jle    529e <overlap+0x6e>
    52ea:	48 39 ca             	cmp    %rcx,%rdx
    52ed:	74 91                	je     5280 <overlap+0x50>
    52ef:	eb d9                	jmp    52ca <overlap+0x9a>
    52f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    52f8:	c3                   	ret
    52f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005300 <verify>:
    5300:	f3 0f 1e fa          	endbr64
    5304:	85 f6                	test   %esi,%esi
    5306:	0f 8e 0a 03 00 00    	jle    5616 <verify+0x316>
    530c:	41 57                	push   %r15
    530e:	45 31 ff             	xor    %r15d,%r15d
    5311:	41 56                	push   %r14
    5313:	41 89 f6             	mov    %esi,%r14d
    5316:	41 55                	push   %r13
    5318:	4c 8d 6f 20          	lea    0x20(%rdi),%r13
    531c:	41 54                	push   %r12
    531e:	55                   	push   %rbp
    531f:	53                   	push   %rbx
    5320:	48 83 ec 48          	sub    $0x48,%rsp
    5324:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
    5329:	4c 89 6c 24 08       	mov    %r13,0x8(%rsp)
    532e:	45 31 e4             	xor    %r12d,%r12d
    5331:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    5336:	45 39 e7             	cmp    %r12d,%r15d
    5339:	0f 84 37 02 00 00    	je     5576 <verify+0x276>
    533f:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5344:	8b 50 08             	mov    0x8(%rax),%edx
    5347:	85 d2                	test   %edx,%edx
    5349:	0f 8e 27 02 00 00    	jle    5576 <verify+0x276>
    534f:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    5358:	31 ed                	xor    %ebp,%ebp
    535a:	44 89 64 24 30       	mov    %r12d,0x30(%rsp)
    535f:	44 89 fa             	mov    %r15d,%edx
    5362:	48 8d 35 ab 0e 00 00 	lea    0xeab(%rip),%rsi        # 6214 <_IO_stdin_used+0x214>
    5369:	bf 01 00 00 00       	mov    $0x1,%edi
    536e:	31 c0                	xor    %eax,%eax
    5370:	e8 bb d0 ff ff       	call   2430 <__printf_chk@plt>
    5375:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    537a:	8b 40 08             	mov    0x8(%rax),%eax
    537d:	85 c0                	test   %eax,%eax
    537f:	0f 8e d2 01 00 00    	jle    5557 <verify+0x257>
    5385:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    538a:	89 6c 24 34          	mov    %ebp,0x34(%rsp)
    538e:	45 31 e4             	xor    %r12d,%r12d
    5391:	44 89 7c 24 38       	mov    %r15d,0x38(%rsp)
    5396:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    539b:	44 89 74 24 3c       	mov    %r14d,0x3c(%rsp)
    53a0:	4c 03 28             	add    (%rax),%r13
    53a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    53a8:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    53ad:	4b 8d 04 e4          	lea    (%r12,%r12,8),%rax
    53b1:	49 8b 4d 60          	mov    0x60(%r13),%rcx
    53b5:	48 8d 35 6d 0e 00 00 	lea    0xe6d(%rip),%rsi        # 6229 <_IO_stdin_used+0x229>
    53bc:	49 8d 2c 44          	lea    (%r12,%rax,2),%rbp
    53c0:	bf 01 00 00 00       	mov    $0x1,%edi
    53c5:	48 8b 03             	mov    (%rbx),%rax
    53c8:	48 c1 e5 03          	shl    $0x3,%rbp
    53cc:	48 01 e8             	add    %rbp,%rax
    53cf:	48 8b 50 60          	mov    0x60(%rax),%rdx
    53d3:	31 c0                	xor    %eax,%eax
    53d5:	e8 56 d0 ff ff       	call   2430 <__printf_chk@plt>
    53da:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    53df:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    53e4:	4c 03 28             	add    (%rax),%r13
    53e7:	49 8b 45 60          	mov    0x60(%r13),%rax
    53eb:	48 85 c0             	test   %rax,%rax
    53ee:	0f 8e 42 01 00 00    	jle    5536 <verify+0x236>
    53f4:	48 8b 13             	mov    (%rbx),%rdx
    53f7:	4c 89 64 24 20       	mov    %r12,0x20(%rsp)
    53fc:	45 31 ff             	xor    %r15d,%r15d
    53ff:	48 01 ea             	add    %rbp,%rdx
    5402:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5408:	48 8b 42 60          	mov    0x60(%rdx),%rax
    540c:	4d 89 fc             	mov    %r15,%r12
    540f:	31 db                	xor    %ebx,%ebx
    5411:	49 c1 e4 05          	shl    $0x5,%r12
    5415:	48 85 c0             	test   %rax,%rax
    5418:	7f 37                	jg     5451 <verify+0x151>
    541a:	e9 01 01 00 00       	jmp    5520 <verify+0x220>
    541f:	90                   	nop
    5420:	48 39 f1             	cmp    %rsi,%rcx
    5423:	0f 8d 67 01 00 00    	jge    5590 <verify+0x290>
    5429:	4d 39 da             	cmp    %r11,%r10
    542c:	7e 09                	jle    5437 <verify+0x137>
    542e:	49 39 c6             	cmp    %rax,%r14
    5431:	0f 8c 81 00 00 00    	jl     54b8 <verify+0x1b8>
    5437:	4d 39 da             	cmp    %r11,%r10
    543a:	0f 8d 9b 01 00 00    	jge    55db <verify+0x2db>
    5440:	48 8b 42 60          	mov    0x60(%rdx),%rax
    5444:	48 83 c3 01          	add    $0x1,%rbx
    5448:	48 39 d8             	cmp    %rbx,%rax
    544b:	0f 8e cf 00 00 00    	jle    5520 <verify+0x220>
    5451:	48 8b 42 50          	mov    0x50(%rdx),%rax
    5455:	49 89 d9             	mov    %rbx,%r9
    5458:	49 8b 4d 50          	mov    0x50(%r13),%rcx
    545c:	49 c1 e1 05          	shl    $0x5,%r9
    5460:	4c 01 e1             	add    %r12,%rcx
    5463:	4c 01 c8             	add    %r9,%rax
    5466:	4c 8b 01             	mov    (%rcx),%r8
    5469:	48 8b 38             	mov    (%rax),%rdi
    546c:	48 8b 71 08          	mov    0x8(%rcx),%rsi
    5470:	4c 8b 59 10          	mov    0x10(%rcx),%r11
    5474:	4c 8b 71 18          	mov    0x18(%rcx),%r14
    5478:	4c 8b 50 10          	mov    0x10(%rax),%r10
    547c:	48 8b 48 08          	mov    0x8(%rax),%rcx
    5480:	48 8b 40 18          	mov    0x18(%rax),%rax
    5484:	4c 39 c7             	cmp    %r8,%rdi
    5487:	7c 97                	jl     5420 <verify+0x120>
    5489:	0f 8e 31 01 00 00    	jle    55c0 <verify+0x2c0>
    548f:	48 39 f1             	cmp    %rsi,%rcx
    5492:	0f 8f 08 01 00 00    	jg     55a0 <verify+0x2a0>
    5498:	75 a6                	jne    5440 <verify+0x140>
    549a:	4d 39 da             	cmp    %r11,%r10
    549d:	7f a1                	jg     5440 <verify+0x140>
    549f:	49 39 c6             	cmp    %rax,%r14
    54a2:	7d 14                	jge    54b8 <verify+0x1b8>
    54a4:	4c 39 c7             	cmp    %r8,%rdi
    54a7:	75 97                	jne    5440 <verify+0x140>
    54a9:	48 39 f1             	cmp    %rsi,%rcx
    54ac:	75 92                	jne    5440 <verify+0x140>
    54ae:	4d 39 da             	cmp    %r11,%r10
    54b1:	75 8d                	jne    5440 <verify+0x140>
    54b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    54b8:	48 8b 72 50          	mov    0x50(%rdx),%rsi
    54bc:	49 8b 45 50          	mov    0x50(%r13),%rax
    54c0:	bf 01 00 00 00       	mov    $0x1,%edi
    54c5:	48 83 c3 01          	add    $0x1,%rbx
    54c9:	48 8b 4a 50          	mov    0x50(%rdx),%rcx
    54cd:	49 8b 55 50          	mov    0x50(%r13),%rdx
    54d1:	4e 8b 44 20 08       	mov    0x8(%rax,%r12,1),%r8
    54d6:	31 c0                	xor    %eax,%eax
    54d8:	4a 8b 4c 09 10       	mov    0x10(%rcx,%r9,1),%rcx
    54dd:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    54e1:	4e 8b 4c 0e 18       	mov    0x18(%rsi,%r9,1),%r9
    54e6:	48 8d 35 db 0e 00 00 	lea    0xedb(%rip),%rsi        # 63c8 <_IO_stdin_used+0x3c8>
    54ed:	e8 3e cf ff ff       	call   2430 <__printf_chk@plt>
    54f2:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    54f7:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    54fc:	4c 03 28             	add    (%rax),%r13
    54ff:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5504:	48 8b 10             	mov    (%rax),%rdx
    5507:	48 01 ea             	add    %rbp,%rdx
    550a:	48 8b 42 60          	mov    0x60(%rdx),%rax
    550e:	48 39 d8             	cmp    %rbx,%rax
    5511:	0f 8f 3a ff ff ff    	jg     5451 <verify+0x151>
    5517:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    5520:	49 8b 45 60          	mov    0x60(%r13),%rax
    5524:	49 83 c7 01          	add    $0x1,%r15
    5528:	4c 39 f8             	cmp    %r15,%rax
    552b:	0f 8f d7 fe ff ff    	jg     5408 <verify+0x108>
    5531:	4c 8b 64 24 20       	mov    0x20(%rsp),%r12
    5536:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    553b:	49 83 c4 01          	add    $0x1,%r12
    553f:	44 39 60 08          	cmp    %r12d,0x8(%rax)
    5543:	0f 8f 5f fe ff ff    	jg     53a8 <verify+0xa8>
    5549:	8b 6c 24 34          	mov    0x34(%rsp),%ebp
    554d:	44 8b 7c 24 38       	mov    0x38(%rsp),%r15d
    5552:	44 8b 74 24 3c       	mov    0x3c(%rsp),%r14d
    5557:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    555c:	83 c5 01             	add    $0x1,%ebp
    555f:	48 81 44 24 18 98 00 00 00 	addq   $0x98,0x18(%rsp)
    5568:	39 68 08             	cmp    %ebp,0x8(%rax)
    556b:	0f 8f ee fd ff ff    	jg     535f <verify+0x5f>
    5571:	44 8b 64 24 30       	mov    0x30(%rsp),%r12d
    5576:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    557b:	48 83 44 24 08 78    	addq   $0x78,0x8(%rsp)
    5581:	41 39 c6             	cmp    %eax,%r14d
    5584:	74 63                	je     55e9 <verify+0x2e9>
    5586:	41 89 c4             	mov    %eax,%r12d
    5589:	e9 a8 fd ff ff       	jmp    5336 <verify+0x36>
    558e:	66 90                	xchg   %ax,%ax
    5590:	0f 85 aa fe ff ff    	jne    5440 <verify+0x140>
    5596:	e9 9c fe ff ff       	jmp    5437 <verify+0x137>
    559b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    55a0:	49 39 c6             	cmp    %rax,%r14
    55a3:	0f 8e f1 fe ff ff    	jle    549a <verify+0x19a>
    55a9:	4d 39 da             	cmp    %r11,%r10
    55ac:	0f 8d e8 fe ff ff    	jge    549a <verify+0x19a>
    55b2:	e9 01 ff ff ff       	jmp    54b8 <verify+0x1b8>
    55b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    55c0:	48 39 f1             	cmp    %rsi,%rcx
    55c3:	0f 8c 6e fe ff ff    	jl     5437 <verify+0x137>
    55c9:	4d 39 da             	cmp    %r11,%r10
    55cc:	0f 8e cd fe ff ff    	jle    549f <verify+0x19f>
    55d2:	48 39 f1             	cmp    %rsi,%rcx
    55d5:	0f 85 65 fe ff ff    	jne    5440 <verify+0x140>
    55db:	49 39 c6             	cmp    %rax,%r14
    55de:	0f 8f 5c fe ff ff    	jg     5440 <verify+0x140>
    55e4:	e9 cf fe ff ff       	jmp    54b8 <verify+0x1b8>
    55e9:	48 83 44 24 10 78    	addq   $0x78,0x10(%rsp)
    55ef:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    55f4:	41 8d 47 01          	lea    0x1(%r15),%eax
    55f8:	45 39 e7             	cmp    %r12d,%r15d
    55fb:	74 08                	je     5605 <verify+0x305>
    55fd:	41 89 c7             	mov    %eax,%r15d
    5600:	e9 24 fd ff ff       	jmp    5329 <verify+0x29>
    5605:	48 83 c4 48          	add    $0x48,%rsp
    5609:	31 c0                	xor    %eax,%eax
    560b:	5b                   	pop    %rbx
    560c:	5d                   	pop    %rbp
    560d:	41 5c                	pop    %r12
    560f:	41 5d                	pop    %r13
    5611:	41 5e                	pop    %r14
    5613:	41 5f                	pop    %r15
    5615:	c3                   	ret
    5616:	31 c0                	xor    %eax,%eax
    5618:	c3                   	ret

Disassembly of section .fini:

000000000000561c <_fini>:
    561c:	f3 0f 1e fa          	endbr64
    5620:	48 83 ec 08          	sub    $0x8,%rsp
    5624:	48 83 c4 08          	add    $0x8,%rsp
    5628:	c3                   	ret
