
multibarrier-evented:     file format elf64-x86-64


Disassembly of section .init:

0000000000004000 <_init>:
    4000:	f3 0f 1e fa          	endbr64
    4004:	48 83 ec 08          	sub    $0x8,%rsp
    4008:	48 8b 05 c9 ff 00 00 	mov    0xffc9(%rip),%rax        # 13fd8 <__gmon_start__@Base>
    400f:	48 85 c0             	test   %rax,%rax
    4012:	74 02                	je     4016 <_init+0x16>
    4014:	ff d0                	call   *%rax
    4016:	48 83 c4 08          	add    $0x8,%rsp
    401a:	c3                   	ret

Disassembly of section .plt:

0000000000004020 <.plt>:
    4020:	ff 35 a2 fd 00 00    	push   0xfda2(%rip)        # 13dc8 <_GLOBAL_OFFSET_TABLE_+0x8>
    4026:	ff 25 a4 fd 00 00    	jmp    *0xfda4(%rip)        # 13dd0 <_GLOBAL_OFFSET_TABLE_+0x10>
    402c:	0f 1f 40 00          	nopl   0x0(%rax)
    4030:	f3 0f 1e fa          	endbr64
    4034:	68 00 00 00 00       	push   $0x0
    4039:	e9 e2 ff ff ff       	jmp    4020 <_init+0x20>
    403e:	66 90                	xchg   %ax,%ax
    4040:	f3 0f 1e fa          	endbr64
    4044:	68 01 00 00 00       	push   $0x1
    4049:	e9 d2 ff ff ff       	jmp    4020 <_init+0x20>
    404e:	66 90                	xchg   %ax,%ax
    4050:	f3 0f 1e fa          	endbr64
    4054:	68 02 00 00 00       	push   $0x2
    4059:	e9 c2 ff ff ff       	jmp    4020 <_init+0x20>
    405e:	66 90                	xchg   %ax,%ax
    4060:	f3 0f 1e fa          	endbr64
    4064:	68 03 00 00 00       	push   $0x3
    4069:	e9 b2 ff ff ff       	jmp    4020 <_init+0x20>
    406e:	66 90                	xchg   %ax,%ax
    4070:	f3 0f 1e fa          	endbr64
    4074:	68 04 00 00 00       	push   $0x4
    4079:	e9 a2 ff ff ff       	jmp    4020 <_init+0x20>
    407e:	66 90                	xchg   %ax,%ax
    4080:	f3 0f 1e fa          	endbr64
    4084:	68 05 00 00 00       	push   $0x5
    4089:	e9 92 ff ff ff       	jmp    4020 <_init+0x20>
    408e:	66 90                	xchg   %ax,%ax
    4090:	f3 0f 1e fa          	endbr64
    4094:	68 06 00 00 00       	push   $0x6
    4099:	e9 82 ff ff ff       	jmp    4020 <_init+0x20>
    409e:	66 90                	xchg   %ax,%ax
    40a0:	f3 0f 1e fa          	endbr64
    40a4:	68 07 00 00 00       	push   $0x7
    40a9:	e9 72 ff ff ff       	jmp    4020 <_init+0x20>
    40ae:	66 90                	xchg   %ax,%ax
    40b0:	f3 0f 1e fa          	endbr64
    40b4:	68 08 00 00 00       	push   $0x8
    40b9:	e9 62 ff ff ff       	jmp    4020 <_init+0x20>
    40be:	66 90                	xchg   %ax,%ax
    40c0:	f3 0f 1e fa          	endbr64
    40c4:	68 09 00 00 00       	push   $0x9
    40c9:	e9 52 ff ff ff       	jmp    4020 <_init+0x20>
    40ce:	66 90                	xchg   %ax,%ax
    40d0:	f3 0f 1e fa          	endbr64
    40d4:	68 0a 00 00 00       	push   $0xa
    40d9:	e9 42 ff ff ff       	jmp    4020 <_init+0x20>
    40de:	66 90                	xchg   %ax,%ax
    40e0:	f3 0f 1e fa          	endbr64
    40e4:	68 0b 00 00 00       	push   $0xb
    40e9:	e9 32 ff ff ff       	jmp    4020 <_init+0x20>
    40ee:	66 90                	xchg   %ax,%ax
    40f0:	f3 0f 1e fa          	endbr64
    40f4:	68 0c 00 00 00       	push   $0xc
    40f9:	e9 22 ff ff ff       	jmp    4020 <_init+0x20>
    40fe:	66 90                	xchg   %ax,%ax
    4100:	f3 0f 1e fa          	endbr64
    4104:	68 0d 00 00 00       	push   $0xd
    4109:	e9 12 ff ff ff       	jmp    4020 <_init+0x20>
    410e:	66 90                	xchg   %ax,%ax
    4110:	f3 0f 1e fa          	endbr64
    4114:	68 0e 00 00 00       	push   $0xe
    4119:	e9 02 ff ff ff       	jmp    4020 <_init+0x20>
    411e:	66 90                	xchg   %ax,%ax
    4120:	f3 0f 1e fa          	endbr64
    4124:	68 0f 00 00 00       	push   $0xf
    4129:	e9 f2 fe ff ff       	jmp    4020 <_init+0x20>
    412e:	66 90                	xchg   %ax,%ax
    4130:	f3 0f 1e fa          	endbr64
    4134:	68 10 00 00 00       	push   $0x10
    4139:	e9 e2 fe ff ff       	jmp    4020 <_init+0x20>
    413e:	66 90                	xchg   %ax,%ax
    4140:	f3 0f 1e fa          	endbr64
    4144:	68 11 00 00 00       	push   $0x11
    4149:	e9 d2 fe ff ff       	jmp    4020 <_init+0x20>
    414e:	66 90                	xchg   %ax,%ax
    4150:	f3 0f 1e fa          	endbr64
    4154:	68 12 00 00 00       	push   $0x12
    4159:	e9 c2 fe ff ff       	jmp    4020 <_init+0x20>
    415e:	66 90                	xchg   %ax,%ax
    4160:	f3 0f 1e fa          	endbr64
    4164:	68 13 00 00 00       	push   $0x13
    4169:	e9 b2 fe ff ff       	jmp    4020 <_init+0x20>
    416e:	66 90                	xchg   %ax,%ax
    4170:	f3 0f 1e fa          	endbr64
    4174:	68 14 00 00 00       	push   $0x14
    4179:	e9 a2 fe ff ff       	jmp    4020 <_init+0x20>
    417e:	66 90                	xchg   %ax,%ax
    4180:	f3 0f 1e fa          	endbr64
    4184:	68 15 00 00 00       	push   $0x15
    4189:	e9 92 fe ff ff       	jmp    4020 <_init+0x20>
    418e:	66 90                	xchg   %ax,%ax
    4190:	f3 0f 1e fa          	endbr64
    4194:	68 16 00 00 00       	push   $0x16
    4199:	e9 82 fe ff ff       	jmp    4020 <_init+0x20>
    419e:	66 90                	xchg   %ax,%ax
    41a0:	f3 0f 1e fa          	endbr64
    41a4:	68 17 00 00 00       	push   $0x17
    41a9:	e9 72 fe ff ff       	jmp    4020 <_init+0x20>
    41ae:	66 90                	xchg   %ax,%ax
    41b0:	f3 0f 1e fa          	endbr64
    41b4:	68 18 00 00 00       	push   $0x18
    41b9:	e9 62 fe ff ff       	jmp    4020 <_init+0x20>
    41be:	66 90                	xchg   %ax,%ax
    41c0:	f3 0f 1e fa          	endbr64
    41c4:	68 19 00 00 00       	push   $0x19
    41c9:	e9 52 fe ff ff       	jmp    4020 <_init+0x20>
    41ce:	66 90                	xchg   %ax,%ax
    41d0:	f3 0f 1e fa          	endbr64
    41d4:	68 1a 00 00 00       	push   $0x1a
    41d9:	e9 42 fe ff ff       	jmp    4020 <_init+0x20>
    41de:	66 90                	xchg   %ax,%ax
    41e0:	f3 0f 1e fa          	endbr64
    41e4:	68 1b 00 00 00       	push   $0x1b
    41e9:	e9 32 fe ff ff       	jmp    4020 <_init+0x20>
    41ee:	66 90                	xchg   %ax,%ax
    41f0:	f3 0f 1e fa          	endbr64
    41f4:	68 1c 00 00 00       	push   $0x1c
    41f9:	e9 22 fe ff ff       	jmp    4020 <_init+0x20>
    41fe:	66 90                	xchg   %ax,%ax
    4200:	f3 0f 1e fa          	endbr64
    4204:	68 1d 00 00 00       	push   $0x1d
    4209:	e9 12 fe ff ff       	jmp    4020 <_init+0x20>
    420e:	66 90                	xchg   %ax,%ax
    4210:	f3 0f 1e fa          	endbr64
    4214:	68 1e 00 00 00       	push   $0x1e
    4219:	e9 02 fe ff ff       	jmp    4020 <_init+0x20>
    421e:	66 90                	xchg   %ax,%ax
    4220:	f3 0f 1e fa          	endbr64
    4224:	68 1f 00 00 00       	push   $0x1f
    4229:	e9 f2 fd ff ff       	jmp    4020 <_init+0x20>
    422e:	66 90                	xchg   %ax,%ax
    4230:	f3 0f 1e fa          	endbr64
    4234:	68 20 00 00 00       	push   $0x20
    4239:	e9 e2 fd ff ff       	jmp    4020 <_init+0x20>
    423e:	66 90                	xchg   %ax,%ax
    4240:	f3 0f 1e fa          	endbr64
    4244:	68 21 00 00 00       	push   $0x21
    4249:	e9 d2 fd ff ff       	jmp    4020 <_init+0x20>
    424e:	66 90                	xchg   %ax,%ax
    4250:	f3 0f 1e fa          	endbr64
    4254:	68 22 00 00 00       	push   $0x22
    4259:	e9 c2 fd ff ff       	jmp    4020 <_init+0x20>
    425e:	66 90                	xchg   %ax,%ax
    4260:	f3 0f 1e fa          	endbr64
    4264:	68 23 00 00 00       	push   $0x23
    4269:	e9 b2 fd ff ff       	jmp    4020 <_init+0x20>
    426e:	66 90                	xchg   %ax,%ax
    4270:	f3 0f 1e fa          	endbr64
    4274:	68 24 00 00 00       	push   $0x24
    4279:	e9 a2 fd ff ff       	jmp    4020 <_init+0x20>
    427e:	66 90                	xchg   %ax,%ax
    4280:	f3 0f 1e fa          	endbr64
    4284:	68 25 00 00 00       	push   $0x25
    4289:	e9 92 fd ff ff       	jmp    4020 <_init+0x20>
    428e:	66 90                	xchg   %ax,%ax
    4290:	f3 0f 1e fa          	endbr64
    4294:	68 26 00 00 00       	push   $0x26
    4299:	e9 82 fd ff ff       	jmp    4020 <_init+0x20>
    429e:	66 90                	xchg   %ax,%ax
    42a0:	f3 0f 1e fa          	endbr64
    42a4:	68 27 00 00 00       	push   $0x27
    42a9:	e9 72 fd ff ff       	jmp    4020 <_init+0x20>
    42ae:	66 90                	xchg   %ax,%ax
    42b0:	f3 0f 1e fa          	endbr64
    42b4:	68 28 00 00 00       	push   $0x28
    42b9:	e9 62 fd ff ff       	jmp    4020 <_init+0x20>
    42be:	66 90                	xchg   %ax,%ax
    42c0:	f3 0f 1e fa          	endbr64
    42c4:	68 29 00 00 00       	push   $0x29
    42c9:	e9 52 fd ff ff       	jmp    4020 <_init+0x20>
    42ce:	66 90                	xchg   %ax,%ax
    42d0:	f3 0f 1e fa          	endbr64
    42d4:	68 2a 00 00 00       	push   $0x2a
    42d9:	e9 42 fd ff ff       	jmp    4020 <_init+0x20>
    42de:	66 90                	xchg   %ax,%ax
    42e0:	f3 0f 1e fa          	endbr64
    42e4:	68 2b 00 00 00       	push   $0x2b
    42e9:	e9 32 fd ff ff       	jmp    4020 <_init+0x20>
    42ee:	66 90                	xchg   %ax,%ax
    42f0:	f3 0f 1e fa          	endbr64
    42f4:	68 2c 00 00 00       	push   $0x2c
    42f9:	e9 22 fd ff ff       	jmp    4020 <_init+0x20>
    42fe:	66 90                	xchg   %ax,%ax
    4300:	f3 0f 1e fa          	endbr64
    4304:	68 2d 00 00 00       	push   $0x2d
    4309:	e9 12 fd ff ff       	jmp    4020 <_init+0x20>
    430e:	66 90                	xchg   %ax,%ax
    4310:	f3 0f 1e fa          	endbr64
    4314:	68 2e 00 00 00       	push   $0x2e
    4319:	e9 02 fd ff ff       	jmp    4020 <_init+0x20>
    431e:	66 90                	xchg   %ax,%ax
    4320:	f3 0f 1e fa          	endbr64
    4324:	68 2f 00 00 00       	push   $0x2f
    4329:	e9 f2 fc ff ff       	jmp    4020 <_init+0x20>
    432e:	66 90                	xchg   %ax,%ax
    4330:	f3 0f 1e fa          	endbr64
    4334:	68 30 00 00 00       	push   $0x30
    4339:	e9 e2 fc ff ff       	jmp    4020 <_init+0x20>
    433e:	66 90                	xchg   %ax,%ax
    4340:	f3 0f 1e fa          	endbr64
    4344:	68 31 00 00 00       	push   $0x31
    4349:	e9 d2 fc ff ff       	jmp    4020 <_init+0x20>
    434e:	66 90                	xchg   %ax,%ax
    4350:	f3 0f 1e fa          	endbr64
    4354:	68 32 00 00 00       	push   $0x32
    4359:	e9 c2 fc ff ff       	jmp    4020 <_init+0x20>
    435e:	66 90                	xchg   %ax,%ax
    4360:	f3 0f 1e fa          	endbr64
    4364:	68 33 00 00 00       	push   $0x33
    4369:	e9 b2 fc ff ff       	jmp    4020 <_init+0x20>
    436e:	66 90                	xchg   %ax,%ax
    4370:	f3 0f 1e fa          	endbr64
    4374:	68 34 00 00 00       	push   $0x34
    4379:	e9 a2 fc ff ff       	jmp    4020 <_init+0x20>
    437e:	66 90                	xchg   %ax,%ax
    4380:	f3 0f 1e fa          	endbr64
    4384:	68 35 00 00 00       	push   $0x35
    4389:	e9 92 fc ff ff       	jmp    4020 <_init+0x20>
    438e:	66 90                	xchg   %ax,%ax
    4390:	f3 0f 1e fa          	endbr64
    4394:	68 36 00 00 00       	push   $0x36
    4399:	e9 82 fc ff ff       	jmp    4020 <_init+0x20>
    439e:	66 90                	xchg   %ax,%ax
    43a0:	f3 0f 1e fa          	endbr64
    43a4:	68 37 00 00 00       	push   $0x37
    43a9:	e9 72 fc ff ff       	jmp    4020 <_init+0x20>
    43ae:	66 90                	xchg   %ax,%ax
    43b0:	f3 0f 1e fa          	endbr64
    43b4:	68 38 00 00 00       	push   $0x38
    43b9:	e9 62 fc ff ff       	jmp    4020 <_init+0x20>
    43be:	66 90                	xchg   %ax,%ax
    43c0:	f3 0f 1e fa          	endbr64
    43c4:	68 39 00 00 00       	push   $0x39
    43c9:	e9 52 fc ff ff       	jmp    4020 <_init+0x20>
    43ce:	66 90                	xchg   %ax,%ax
    43d0:	f3 0f 1e fa          	endbr64
    43d4:	68 3a 00 00 00       	push   $0x3a
    43d9:	e9 42 fc ff ff       	jmp    4020 <_init+0x20>
    43de:	66 90                	xchg   %ax,%ax
    43e0:	f3 0f 1e fa          	endbr64
    43e4:	68 3b 00 00 00       	push   $0x3b
    43e9:	e9 32 fc ff ff       	jmp    4020 <_init+0x20>
    43ee:	66 90                	xchg   %ax,%ax
    43f0:	f3 0f 1e fa          	endbr64
    43f4:	68 3c 00 00 00       	push   $0x3c
    43f9:	e9 22 fc ff ff       	jmp    4020 <_init+0x20>
    43fe:	66 90                	xchg   %ax,%ax
    4400:	f3 0f 1e fa          	endbr64
    4404:	68 3d 00 00 00       	push   $0x3d
    4409:	e9 12 fc ff ff       	jmp    4020 <_init+0x20>
    440e:	66 90                	xchg   %ax,%ax
    4410:	f3 0f 1e fa          	endbr64
    4414:	68 3e 00 00 00       	push   $0x3e
    4419:	e9 02 fc ff ff       	jmp    4020 <_init+0x20>
    441e:	66 90                	xchg   %ax,%ax
    4420:	f3 0f 1e fa          	endbr64
    4424:	68 3f 00 00 00       	push   $0x3f
    4429:	e9 f2 fb ff ff       	jmp    4020 <_init+0x20>
    442e:	66 90                	xchg   %ax,%ax

Disassembly of section .plt.got:

0000000000004430 <__cxa_finalize@plt>:
    4430:	f3 0f 1e fa          	endbr64
    4434:	ff 25 b6 fb 00 00    	jmp    *0xfbb6(%rip)        # 13ff0 <__cxa_finalize@GLIBC_2.2.5>
    443a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

0000000000004440 <pthread_setaffinity_np@plt>:
    4440:	f3 0f 1e fa          	endbr64
    4444:	ff 25 8e f9 00 00    	jmp    *0xf98e(%rip)        # 13dd8 <pthread_setaffinity_np@GLIBC_2.34>
    444a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004450 <__asan_poison_stack_memory@plt>:
    4450:	f3 0f 1e fa          	endbr64
    4454:	ff 25 86 f9 00 00    	jmp    *0xf986(%rip)        # 13de0 <__asan_poison_stack_memory@Base>
    445a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004460 <calloc@plt>:
    4460:	f3 0f 1e fa          	endbr64
    4464:	ff 25 7e f9 00 00    	jmp    *0xf97e(%rip)        # 13de8 <calloc@Base>
    446a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004470 <io_uring_queue_init@plt>:
    4470:	f3 0f 1e fa          	endbr64
    4474:	ff 25 76 f9 00 00    	jmp    *0xf976(%rip)        # 13df0 <io_uring_queue_init@LIBURING_2.0>
    447a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004480 <clock_gettime@plt>:
    4480:	f3 0f 1e fa          	endbr64
    4484:	ff 25 6e f9 00 00    	jmp    *0xf96e(%rip)        # 13df8 <clock_gettime@Base>
    448a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004490 <close@plt>:
    4490:	f3 0f 1e fa          	endbr64
    4494:	ff 25 66 f9 00 00    	jmp    *0xf966(%rip)        # 13e00 <close@GLIBC_2.2.5>
    449a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000044a0 <fwrite@plt>:
    44a0:	f3 0f 1e fa          	endbr64
    44a4:	ff 25 5e f9 00 00    	jmp    *0xf95e(%rip)        # 13e08 <fwrite@Base>
    44aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000044b0 <__asan_init@plt>:
    44b0:	f3 0f 1e fa          	endbr64
    44b4:	ff 25 56 f9 00 00    	jmp    *0xf956(%rip)        # 13e10 <__asan_init@Base>
    44ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000044c0 <memcpy@plt>:
    44c0:	f3 0f 1e fa          	endbr64
    44c4:	ff 25 4e f9 00 00    	jmp    *0xf94e(%rip)        # 13e18 <memcpy@Base>
    44ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000044d0 <__asan_stack_malloc_2@plt>:
    44d0:	f3 0f 1e fa          	endbr64
    44d4:	ff 25 46 f9 00 00    	jmp    *0xf946(%rip)        # 13e20 <__asan_stack_malloc_2@Base>
    44da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000044e0 <__asan_report_load8@plt>:
    44e0:	f3 0f 1e fa          	endbr64
    44e4:	ff 25 3e f9 00 00    	jmp    *0xf93e(%rip)        # 13e28 <__asan_report_load8@Base>
    44ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000044f0 <__asan_stack_malloc_1@plt>:
    44f0:	f3 0f 1e fa          	endbr64
    44f4:	ff 25 36 f9 00 00    	jmp    *0xf936(%rip)        # 13e30 <__asan_stack_malloc_1@Base>
    44fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004500 <__asan_report_store2@plt>:
    4500:	f3 0f 1e fa          	endbr64
    4504:	ff 25 2e f9 00 00    	jmp    *0xf92e(%rip)        # 13e38 <__asan_report_store2@Base>
    450a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004510 <exit@plt>:
    4510:	f3 0f 1e fa          	endbr64
    4514:	ff 25 26 f9 00 00    	jmp    *0xf926(%rip)        # 13e40 <exit@GLIBC_2.2.5>
    451a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004520 <__printf_chk@plt>:
    4520:	f3 0f 1e fa          	endbr64
    4524:	ff 25 1e f9 00 00    	jmp    *0xf91e(%rip)        # 13e48 <__printf_chk@GLIBC_2.3.4>
    452a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004530 <putchar@plt>:
    4530:	f3 0f 1e fa          	endbr64
    4534:	ff 25 16 f9 00 00    	jmp    *0xf916(%rip)        # 13e50 <putchar@GLIBC_2.2.5>
    453a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004540 <__asan_stack_malloc_6@plt>:
    4540:	f3 0f 1e fa          	endbr64
    4544:	ff 25 0e f9 00 00    	jmp    *0xf90e(%rip)        # 13e58 <__asan_stack_malloc_6@Base>
    454a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004550 <__asan_report_load4@plt>:
    4550:	f3 0f 1e fa          	endbr64
    4554:	ff 25 06 f9 00 00    	jmp    *0xf906(%rip)        # 13e60 <__asan_report_load4@Base>
    455a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004560 <__asan_report_load_n@plt>:
    4560:	f3 0f 1e fa          	endbr64
    4564:	ff 25 fe f8 00 00    	jmp    *0xf8fe(%rip)        # 13e68 <__asan_report_load_n@Base>
    456a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004570 <__asan_unpoison_stack_memory@plt>:
    4570:	f3 0f 1e fa          	endbr64
    4574:	ff 25 f6 f8 00 00    	jmp    *0xf8f6(%rip)        # 13e70 <__asan_unpoison_stack_memory@Base>
    457a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004580 <__asan_report_store_n@plt>:
    4580:	f3 0f 1e fa          	endbr64
    4584:	ff 25 ee f8 00 00    	jmp    *0xf8ee(%rip)        # 13e78 <__asan_report_store_n@Base>
    458a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004590 <malloc@plt>:
    4590:	f3 0f 1e fa          	endbr64
    4594:	ff 25 e6 f8 00 00    	jmp    *0xf8e6(%rip)        # 13e80 <malloc@Base>
    459a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000045a0 <strrchr@plt>:
    45a0:	f3 0f 1e fa          	endbr64
    45a4:	ff 25 de f8 00 00    	jmp    *0xf8de(%rip)        # 13e88 <strrchr@Base>
    45aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000045b0 <__memcpy_chk@plt>:
    45b0:	f3 0f 1e fa          	endbr64
    45b4:	ff 25 d6 f8 00 00    	jmp    *0xf8d6(%rip)        # 13e90 <__memcpy_chk@GLIBC_2.3.4>
    45ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000045c0 <setsockopt@plt>:
    45c0:	f3 0f 1e fa          	endbr64
    45c4:	ff 25 ce f8 00 00    	jmp    *0xf8ce(%rip)        # 13e98 <setsockopt@GLIBC_2.2.5>
    45ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000045d0 <eventfd@plt>:
    45d0:	f3 0f 1e fa          	endbr64
    45d4:	ff 25 c6 f8 00 00    	jmp    *0xf8c6(%rip)        # 13ea0 <eventfd@GLIBC_2.7>
    45da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000045e0 <strlen@plt>:
    45e0:	f3 0f 1e fa          	endbr64
    45e4:	ff 25 be f8 00 00    	jmp    *0xf8be(%rip)        # 13ea8 <strlen@Base>
    45ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000045f0 <stat@plt>:
    45f0:	f3 0f 1e fa          	endbr64
    45f4:	ff 25 b6 f8 00 00    	jmp    *0xf8b6(%rip)        # 13eb0 <stat@Base>
    45fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004600 <read@plt>:
    4600:	f3 0f 1e fa          	endbr64
    4604:	ff 25 ae f8 00 00    	jmp    *0xf8ae(%rip)        # 13eb8 <read@Base>
    460a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004610 <__asan_handle_no_return@plt>:
    4610:	f3 0f 1e fa          	endbr64
    4614:	ff 25 a6 f8 00 00    	jmp    *0xf8a6(%rip)        # 13ec0 <__asan_handle_no_return@Base>
    461a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004620 <listen@plt>:
    4620:	f3 0f 1e fa          	endbr64
    4624:	ff 25 9e f8 00 00    	jmp    *0xf89e(%rip)        # 13ec8 <listen@GLIBC_2.2.5>
    462a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004630 <io_uring_register_eventfd@plt>:
    4630:	f3 0f 1e fa          	endbr64
    4634:	ff 25 96 f8 00 00    	jmp    *0xf896(%rip)        # 13ed0 <io_uring_register_eventfd@LIBURING_2.0>
    463a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004640 <strtok_r@plt>:
    4640:	f3 0f 1e fa          	endbr64
    4644:	ff 25 8e f8 00 00    	jmp    *0xf88e(%rip)        # 13ed8 <strtok_r@GLIBC_2.2.5>
    464a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004650 <pthread_create@plt>:
    4650:	f3 0f 1e fa          	endbr64
    4654:	ff 25 86 f8 00 00    	jmp    *0xf886(%rip)        # 13ee0 <pthread_create@Base>
    465a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004660 <io_uring_submit@plt>:
    4660:	f3 0f 1e fa          	endbr64
    4664:	ff 25 7e f8 00 00    	jmp    *0xf87e(%rip)        # 13ee8 <io_uring_submit@LIBURING_2.0>
    466a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004670 <__strcpy_chk@plt>:
    4670:	f3 0f 1e fa          	endbr64
    4674:	ff 25 76 f8 00 00    	jmp    *0xf876(%rip)        # 13ef0 <__strcpy_chk@GLIBC_2.3.4>
    467a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004680 <__asan_stack_free_5@plt>:
    4680:	f3 0f 1e fa          	endbr64
    4684:	ff 25 6e f8 00 00    	jmp    *0xf86e(%rip)        # 13ef8 <__asan_stack_free_5@Base>
    468a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004690 <socket@plt>:
    4690:	f3 0f 1e fa          	endbr64
    4694:	ff 25 66 f8 00 00    	jmp    *0xf866(%rip)        # 13f00 <socket@GLIBC_2.2.5>
    469a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000046a0 <memset@plt>:
    46a0:	f3 0f 1e fa          	endbr64
    46a4:	ff 25 5e f8 00 00    	jmp    *0xf85e(%rip)        # 13f08 <memset@Base>
    46aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000046b0 <__stack_chk_fail@plt>:
    46b0:	f3 0f 1e fa          	endbr64
    46b4:	ff 25 56 f8 00 00    	jmp    *0xf856(%rip)        # 13f10 <__stack_chk_fail@GLIBC_2.4>
    46ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000046c0 <__asan_report_store4@plt>:
    46c0:	f3 0f 1e fa          	endbr64
    46c4:	ff 25 4e f8 00 00    	jmp    *0xf84e(%rip)        # 13f18 <__asan_report_store4@Base>
    46ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000046d0 <__asan_report_store8@plt>:
    46d0:	f3 0f 1e fa          	endbr64
    46d4:	ff 25 46 f8 00 00    	jmp    *0xf846(%rip)        # 13f20 <__asan_report_store8@Base>
    46da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000046e0 <nanosleep@plt>:
    46e0:	f3 0f 1e fa          	endbr64
    46e4:	ff 25 3e f8 00 00    	jmp    *0xf83e(%rip)        # 13f28 <nanosleep@GLIBC_2.2.5>
    46ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000046f0 <__ctype_tolower_loc@plt>:
    46f0:	f3 0f 1e fa          	endbr64
    46f4:	ff 25 36 f8 00 00    	jmp    *0xf836(%rip)        # 13f30 <__ctype_tolower_loc@GLIBC_2.3>
    46fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004700 <__asan_unregister_globals@plt>:
    4700:	f3 0f 1e fa          	endbr64
    4704:	ff 25 2e f8 00 00    	jmp    *0xf82e(%rip)        # 13f38 <__asan_unregister_globals@Base>
    470a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004710 <__asan_stack_free_6@plt>:
    4710:	f3 0f 1e fa          	endbr64
    4714:	ff 25 26 f8 00 00    	jmp    *0xf826(%rip)        # 13f40 <__asan_stack_free_6@Base>
    471a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004720 <__sprintf_chk@plt>:
    4720:	f3 0f 1e fa          	endbr64
    4724:	ff 25 1e f8 00 00    	jmp    *0xf81e(%rip)        # 13f48 <__sprintf_chk@Base>
    472a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004730 <strcmp@plt>:
    4730:	f3 0f 1e fa          	endbr64
    4734:	ff 25 16 f8 00 00    	jmp    *0xf816(%rip)        # 13f50 <strcmp@Base>
    473a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004740 <__io_uring_get_cqe@plt>:
    4740:	f3 0f 1e fa          	endbr64
    4744:	ff 25 0e f8 00 00    	jmp    *0xf80e(%rip)        # 13f58 <__io_uring_get_cqe@LIBURING_2.0>
    474a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004750 <__fprintf_chk@plt>:
    4750:	f3 0f 1e fa          	endbr64
    4754:	ff 25 06 f8 00 00    	jmp    *0xf806(%rip)        # 13f60 <__fprintf_chk@Base>
    475a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004760 <__asan_register_globals@plt>:
    4760:	f3 0f 1e fa          	endbr64
    4764:	ff 25 fe f7 00 00    	jmp    *0xf7fe(%rip)        # 13f68 <__asan_register_globals@Base>
    476a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004770 <__asan_stack_malloc_5@plt>:
    4770:	f3 0f 1e fa          	endbr64
    4774:	ff 25 f6 f7 00 00    	jmp    *0xf7f6(%rip)        # 13f70 <__asan_stack_malloc_5@Base>
    477a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004780 <bind@plt>:
    4780:	f3 0f 1e fa          	endbr64
    4784:	ff 25 ee f7 00 00    	jmp    *0xf7ee(%rip)        # 13f78 <bind@GLIBC_2.2.5>
    478a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004790 <__asan_report_load1@plt>:
    4790:	f3 0f 1e fa          	endbr64
    4794:	ff 25 e6 f7 00 00    	jmp    *0xf7e6(%rip)        # 13f80 <__asan_report_load1@Base>
    479a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000047a0 <free@plt>:
    47a0:	f3 0f 1e fa          	endbr64
    47a4:	ff 25 de f7 00 00    	jmp    *0xf7de(%rip)        # 13f88 <free@Base>
    47aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000047b0 <__asan_stack_malloc_0@plt>:
    47b0:	f3 0f 1e fa          	endbr64
    47b4:	ff 25 d6 f7 00 00    	jmp    *0xf7d6(%rip)        # 13f90 <__asan_stack_malloc_0@Base>
    47ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000047c0 <perror@plt>:
    47c0:	f3 0f 1e fa          	endbr64
    47c4:	ff 25 ce f7 00 00    	jmp    *0xf7ce(%rip)        # 13f98 <perror@GLIBC_2.2.5>
    47ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000047d0 <__asan_report_store1@plt>:
    47d0:	f3 0f 1e fa          	endbr64
    47d4:	ff 25 c6 f7 00 00    	jmp    *0xf7c6(%rip)        # 13fa0 <__asan_report_store1@Base>
    47da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000047e0 <strerror@plt>:
    47e0:	f3 0f 1e fa          	endbr64
    47e4:	ff 25 be f7 00 00    	jmp    *0xf7be(%rip)        # 13fa8 <strerror@Base>
    47ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000047f0 <eventfd_write@plt>:
    47f0:	f3 0f 1e fa          	endbr64
    47f4:	ff 25 b6 f7 00 00    	jmp    *0xf7b6(%rip)        # 13fb0 <eventfd_write@Base>
    47fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004800 <puts@plt>:
    4800:	f3 0f 1e fa          	endbr64
    4804:	ff 25 ae f7 00 00    	jmp    *0xf7ae(%rip)        # 13fb8 <puts@Base>
    480a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004810 <__asan_version_mismatch_check_v8@plt>:
    4810:	f3 0f 1e fa          	endbr64
    4814:	ff 25 a6 f7 00 00    	jmp    *0xf7a6(%rip)        # 13fc0 <__asan_version_mismatch_check_v8@Base>
    481a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004820 <open@plt>:
    4820:	f3 0f 1e fa          	endbr64
    4824:	ff 25 9e f7 00 00    	jmp    *0xf79e(%rip)        # 13fc8 <open@GLIBC_2.2.5>
    482a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004830 <pthread_join@plt>:
    4830:	f3 0f 1e fa          	endbr64
    4834:	ff 25 96 f7 00 00    	jmp    *0xf796(%rip)        # 13fd0 <pthread_join@Base>
    483a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

0000000000004840 <fatal_error>:
struct Snapshot {
  struct timespec start;
  struct timespec end;
};

void fatal_error(const char *syscall) {
    4840:	f3 0f 1e fa          	endbr64
    4844:	50                   	push   %rax
    4845:	58                   	pop    %rax
    4846:	50                   	push   %rax
    perror(syscall);
    4847:	e8 74 ff ff ff       	call   47c0 <perror@plt>
    exit(1);
    484c:	e8 bf fd ff ff       	call   4610 <__asan_handle_no_return@plt>
    4851:	bf 01 00 00 00       	mov    $0x1,%edi
    4856:	e8 b5 fc ff ff       	call   4510 <exit@plt>

000000000000485b <copy_file_contents.cold>:
    int fd;

    char *buf = zh_malloc(file_size);
    fd = open(file_path, O_RDONLY);
    if (fd < 0)
        fatal_error("read");
    485b:	e8 b0 fd ff ff       	call   4610 <__asan_handle_no_return@plt>
    4860:	48 8d 3d b9 bf 00 00 	lea    0xbfb9(%rip),%rdi        # 10820 <_IO_stdin_used+0x820>
    4867:	e8 d4 ff ff ff       	call   4840 <fatal_error>

000000000000486c <add_write_request.cold>:
    iov->iov_base = buf;
    iov->iov_len = file_size;
}
int add_write_request(struct Request *req, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    req->event_type = EVENT_TYPE_WRITE;
    486c:	48 89 d0             	mov    %rdx,%rax
    486f:	48 c1 e8 03          	shr    $0x3,%rax
    4873:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    487a:	84 c0                	test   %al,%al
    487c:	74 04                	je     4882 <add_write_request.cold+0x16>
    487e:	3c 03                	cmp    $0x3,%al
    4880:	7e 1e                	jle    48a0 <add_write_request.cold+0x34>

IOURINGINLINE void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
    4882:	0f b6 04 25 00 80 ff 7f 	movzbl 0x7fff8000,%eax
    488a:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    4890:	84 c0                	test   %al,%al
    4892:	74 02                	je     4896 <add_write_request.cold+0x2a>
    4894:	7e 12                	jle    48a8 <add_write_request.cold+0x3c>
    4896:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    489e:	0f 0b                	ud2
    48a0:	48 89 d7             	mov    %rdx,%rdi
    48a3:	e8 18 fe ff ff       	call   46c0 <__asan_report_store4@plt>
    48a8:	31 ff                	xor    %edi,%edi
    48aa:	e8 21 ff ff ff       	call   47d0 <__asan_report_store1@plt>

00000000000048af <add_read_request.cold>:
    return 0;
}

int add_read_request(int client_socket, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    48af:	bf 20 00 00 00       	mov    $0x20,%edi
    48b4:	e8 d7 fc ff ff       	call   4590 <malloc@plt>
        

    req->iov[0].iov_base = malloc(READ_SZ);
    48b9:	bf 00 20 00 00       	mov    $0x2000,%edi
    48be:	be 01 00 00 00       	mov    $0x1,%esi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    48c3:	48 89 c3             	mov    %rax,%rbx
    req->iov[0].iov_base = malloc(READ_SZ);
    48c6:	e8 95 fb ff ff       	call   4460 <calloc@plt>
    48cb:	48 8d 7b 10          	lea    0x10(%rbx),%rdi
    48cf:	48 89 fa             	mov    %rdi,%rdx
    48d2:	48 c1 ea 03          	shr    $0x3,%rdx
    48d6:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    48dd:	75 72                	jne    4951 <add_read_request.cold+0xa2>
    req->iov[0].iov_len = READ_SZ;
    48df:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    48e3:	48 89 43 10          	mov    %rax,0x10(%rbx)
    req->iov[0].iov_len = READ_SZ;
    48e7:	48 89 f8             	mov    %rdi,%rax
    48ea:	48 c1 e8 03          	shr    $0x3,%rax
    48ee:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    48f5:	75 5f                	jne    4956 <add_read_request.cold+0xa7>
    req->event_type = EVENT_TYPE_READ;
    48f7:	48 89 d8             	mov    %rbx,%rax
    req->iov[0].iov_len = READ_SZ;
    48fa:	48 c7 43 18 00 20 00 00 	movq   $0x2000,0x18(%rbx)
    req->event_type = EVENT_TYPE_READ;
    4902:	48 c1 e8 03          	shr    $0x3,%rax
    4906:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    490d:	84 c0                	test   %al,%al
    490f:	74 04                	je     4915 <add_read_request.cold+0x66>
    4911:	3c 03                	cmp    $0x3,%al
    4913:	7e 46                	jle    495b <add_read_request.cold+0xac>
    req->client_socket = client_socket;
    4915:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    req->event_type = EVENT_TYPE_READ;
    4919:	c7 03 01 00 00 00    	movl   $0x1,(%rbx)
    req->client_socket = client_socket;
    491f:	48 89 f8             	mov    %rdi,%rax
    4922:	48 c1 e8 03          	shr    $0x3,%rax
    4926:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    492d:	84 c0                	test   %al,%al
    492f:	74 04                	je     4935 <add_read_request.cold+0x86>
    4931:	3c 03                	cmp    $0x3,%al
    4933:	7e 2e                	jle    4963 <add_read_request.cold+0xb4>
    4935:	0f b6 04 25 00 80 ff 7f 	movzbl 0x7fff8000,%eax
    493d:	44 89 6b 08          	mov    %r13d,0x8(%rbx)
    4941:	84 c0                	test   %al,%al
    4943:	74 02                	je     4947 <add_read_request.cold+0x98>
    4945:	7e 21                	jle    4968 <add_read_request.cold+0xb9>
    4947:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    494f:	0f 0b                	ud2
    req->iov[0].iov_base = malloc(READ_SZ);
    4951:	e8 7a fd ff ff       	call   46d0 <__asan_report_store8@plt>
    req->iov[0].iov_len = READ_SZ;
    4956:	e8 75 fd ff ff       	call   46d0 <__asan_report_store8@plt>
    req->event_type = EVENT_TYPE_READ;
    495b:	48 89 df             	mov    %rbx,%rdi
    495e:	e8 5d fd ff ff       	call   46c0 <__asan_report_store4@plt>
    req->client_socket = client_socket;
    4963:	e8 58 fd ff ff       	call   46c0 <__asan_report_store4@plt>
    4968:	31 ff                	xor    %edi,%edi
    496a:	e8 61 fe ff ff       	call   47d0 <__asan_report_store1@plt>

000000000000496f <_send_static_string_content.cold>:
    req->event_type = EVENT_TYPE_WRITE;
    496f:	48 89 e8             	mov    %rbp,%rax
    4972:	48 c1 e8 03          	shr    $0x3,%rax
    4976:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    497d:	84 c0                	test   %al,%al
    497f:	74 04                	je     4985 <_send_static_string_content.cold+0x16>
    4981:	3c 03                	cmp    $0x3,%al
    4983:	7e 1f                	jle    49a4 <_send_static_string_content.cold+0x35>
    4985:	0f b6 04 25 00 80 ff 7f 	movzbl 0x7fff8000,%eax
    498d:	c7 45 00 02 00 00 00 	movl   $0x2,0x0(%rbp)
    4994:	84 c0                	test   %al,%al
    4996:	74 02                	je     499a <_send_static_string_content.cold+0x2b>
    4998:	7e 12                	jle    49ac <_send_static_string_content.cold+0x3d>
    499a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    49a2:	0f 0b                	ud2
    49a4:	48 89 ef             	mov    %rbp,%rdi
    49a7:	e8 14 fd ff ff       	call   46c0 <__asan_report_store4@plt>
    49ac:	31 ff                	xor    %edi,%edi
    49ae:	e8 1d fe ff ff       	call   47d0 <__asan_report_store1@plt>

00000000000049b3 <add_accept_request.cold>:
    49b3:	0f b6 04 25 00 80 ff 7f 	movzbl 0x7fff8000,%eax
    49bb:	84 c0                	test   %al,%al
    49bd:	74 02                	je     49c1 <add_accept_request.cold+0xe>
    49bf:	7e 0a                	jle    49cb <add_accept_request.cold+0x18>
    49c1:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    49c9:	0f 0b                	ud2
    49cb:	31 ff                	xor    %edi,%edi
    49cd:	e8 fe fd ff ff       	call   47d0 <__asan_report_store1@plt>

00000000000049d2 <io_thread.cold>:
    49d2:	0f b6 04 25 00 80 ff 7f 	movzbl 0x7fff8000,%eax
    49da:	84 c0                	test   %al,%al
    49dc:	74 02                	je     49e0 <io_thread.cold+0xe>
    49de:	7e 2c                	jle    4a0c <io_thread.cold+0x3a>
    49e0:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    49e8:	0f 0b                	ud2
           (const struct sockaddr *)&srv_addr,
           sizeof(srv_addr)) < 0)
      fatal_error("bind()");

  if (listen(sock, 10) < 0) {
    fatal_error("listen()");
    49ea:	e8 21 fc ff ff       	call   4610 <__asan_handle_no_return@plt>
    49ef:	48 8d 3d 6a c1 00 00 	lea    0xc16a(%rip),%rdi        # 10b60 <_IO_stdin_used+0xb60>
    49f6:	e8 45 fe ff ff       	call   4840 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    49fb:	e8 10 fc ff ff       	call   4610 <__asan_handle_no_return@plt>
    4a00:	48 8d 3d d9 c0 00 00 	lea    0xc0d9(%rip),%rdi        # 10ae0 <_IO_stdin_used+0xae0>
    4a07:	e8 34 fe ff ff       	call   4840 <fatal_error>
    4a0c:	31 ff                	xor    %edi,%edi
    4a0e:	e8 bd fd ff ff       	call   47d0 <__asan_report_store1@plt>
        break;
      }
      printf("Received wait finished\n");
      struct Request *req = (struct Request *) cqe->user_data;
      if (ret < 0)
          fatal_error("io_uring_wait_cqe");
    4a13:	e8 f8 fb ff ff       	call   4610 <__asan_handle_no_return@plt>
    4a18:	48 8d 3d 81 c2 00 00 	lea    0xc281(%rip),%rdi        # 10ca0 <_IO_stdin_used+0xca0>
    4a1f:	e8 1c fe ff ff       	call   4840 <fatal_error>
      fatal_error("bind()");
    4a24:	e8 e7 fb ff ff       	call   4610 <__asan_handle_no_return@plt>
    4a29:	48 8d 3d f0 c0 00 00 	lea    0xc0f0(%rip),%rdi        # 10b20 <_IO_stdin_used+0xb20>
    4a30:	e8 0b fe ff ff       	call   4840 <fatal_error>
    4a35:	0f b6 04 25 00 80 ff 7f 	movzbl 0x7fff8000,%eax
    4a3d:	84 c0                	test   %al,%al
    4a3f:	74 02                	je     4a43 <io_thread.cold+0x71>
    4a41:	7e 1b                	jle    4a5e <io_thread.cold+0x8c>
    4a43:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    4a4b:	0f 0b                	ud2
      fatal_error("socket()");
    4a4d:	e8 be fb ff ff       	call   4610 <__asan_handle_no_return@plt>
    4a52:	48 8d 3d 47 c0 00 00 	lea    0xc047(%rip),%rdi        # 10aa0 <_IO_stdin_used+0xaa0>
    4a59:	e8 e2 fd ff ff       	call   4840 <fatal_error>
    4a5e:	31 ff                	xor    %edi,%edi
    4a60:	e8 6b fd ff ff       	call   47d0 <__asan_report_store1@plt>
    4a65:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4a6f:	90                   	nop

0000000000004a70 <_sub_D_00099_0>:
  printf("Total sents %ld\n", sents / DURATION);
  printf("Total receives %ld\n", received / DURATION);
  // verify(thread_data, thread_count);
  return 0;

}
    4a70:	f3 0f 1e fa          	endbr64
    4a74:	be 6b 00 00 00       	mov    $0x6b,%esi
    4a79:	48 8d 3d 40 f6 00 00 	lea    0xf640(%rip),%rdi        # 140c0 <unimplemented_content+0x60>
    4a80:	e9 7b fc ff ff       	jmp    4700 <__asan_unregister_globals@plt>
    4a85:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4a8f:	90                   	nop

0000000000004a90 <main>:
int main() {
    4a90:	f3 0f 1e fa          	endbr64
    4a94:	41 57                	push   %r15
    4a96:	41 56                	push   %r14
    4a98:	41 55                	push   %r13
    4a9a:	41 54                	push   %r12
    4a9c:	55                   	push   %rbp
    4a9d:	53                   	push   %rbx
    4a9e:	48 81 ec 28 01 00 00 	sub    $0x128,%rsp
    4aa5:	44 8b 0d d4 10 01 00 	mov    0x110d4(%rip),%r9d        # 15b80 <__asan_option_detect_stack_use_after_return@@Base>
    4aac:	48 8d 84 24 c0 00 00 00 	lea    0xc0(%rsp),%rax
    4ab4:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
    4abc:	48 89 84 24 b0 00 00 00 	mov    %rax,0xb0(%rsp)
    4ac4:	45 85 c9             	test   %r9d,%r9d
    4ac7:	0f 85 64 2b 00 00    	jne    7631 <main+0x2ba1>
    4acd:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4ad5:	48 8d 3d 64 c5 00 00 	lea    0xc564(%rip),%rdi        # 11040 <_IO_stdin_used+0x1040>
    4adc:	48 8d 58 60          	lea    0x60(%rax),%rbx
    4ae0:	48 89 9c 24 b8 00 00 00 	mov    %rbx,0xb8(%rsp)
    4ae8:	48 8d 1d 65 d6 00 00 	lea    0xd665(%rip),%rbx        # 12154 <_IO_stdin_used+0x2154>
    4aef:	48 89 58 08          	mov    %rbx,0x8(%rax)
    4af3:	48 8d 1d 96 ff ff ff 	lea    -0x6a(%rip),%rbx        # 4a90 <main>
    4afa:	48 89 58 10          	mov    %rbx,0x10(%rax)
    4afe:	48 c7 00 b3 8a b5 41 	movq   $0x41b58ab3,(%rax)
    4b05:	48 c1 e8 03          	shr    $0x3,%rax
    4b09:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
    4b11:	c7 80 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%rax)
    4b1b:	c7 80 04 80 ff 7f 00 f3 f3 f3 	movl   $0xf3f3f300,0x7fff8004(%rax)
    4b25:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4b2e:	48 89 84 24 18 01 00 00 	mov    %rax,0x118(%rsp)
    4b36:	31 c0                	xor    %eax,%eax
    4b38:	e8 c3 fc ff ff       	call   4800 <puts@plt>
    4b3d:	bf 0a 00 00 00       	mov    $0xa,%edi
    4b42:	e8 e9 f9 ff ff       	call   4530 <putchar@plt>
    4b47:	ba 0c 00 00 00       	mov    $0xc,%edx
    4b4c:	48 8d 35 8d c5 00 00 	lea    0xc58d(%rip),%rsi        # 110e0 <_IO_stdin_used+0x10e0>
    4b53:	31 c0                	xor    %eax,%eax
    4b55:	bf 01 00 00 00       	mov    $0x1,%edi
    4b5a:	e8 c1 f9 ff ff       	call   4520 <__printf_chk@plt>
    4b5f:	48 8d 3d ba c5 00 00 	lea    0xc5ba(%rip),%rdi        # 11120 <_IO_stdin_used+0x1120>
    4b66:	e8 95 fc ff ff       	call   4800 <puts@plt>
    4b6b:	ba 02 00 00 00       	mov    $0x2,%edx
    4b70:	48 8d 35 e9 c5 00 00 	lea    0xc5e9(%rip),%rsi        # 11160 <_IO_stdin_used+0x1160>
    4b77:	31 c0                	xor    %eax,%eax
    4b79:	bf 01 00 00 00       	mov    $0x1,%edi
    4b7e:	e8 9d f9 ff ff       	call   4520 <__printf_chk@plt>
    4b83:	ba 10 00 00 00       	mov    $0x10,%edx
    4b88:	48 8d 35 11 c6 00 00 	lea    0xc611(%rip),%rsi        # 111a0 <_IO_stdin_used+0x11a0>
    4b8f:	31 c0                	xor    %eax,%eax
    4b91:	bf 01 00 00 00       	mov    $0x1,%edi
    4b96:	e8 85 f9 ff ff       	call   4520 <__printf_chk@plt>
    4b9b:	ba 01 00 00 00       	mov    $0x1,%edx
    4ba0:	48 8d 35 39 c6 00 00 	lea    0xc639(%rip),%rsi        # 111e0 <_IO_stdin_used+0x11e0>
    4ba7:	31 c0                	xor    %eax,%eax
    4ba9:	bf 01 00 00 00       	mov    $0x1,%edi
    4bae:	e8 6d f9 ff ff       	call   4520 <__printf_chk@plt>
    4bb3:	ba 01 00 00 00       	mov    $0x1,%edx
    4bb8:	48 8d 35 61 c6 00 00 	lea    0xc661(%rip),%rsi        # 11220 <_IO_stdin_used+0x1220>
    4bbf:	31 c0                	xor    %eax,%eax
    4bc1:	bf 01 00 00 00       	mov    $0x1,%edi
    4bc6:	e8 55 f9 ff ff       	call   4520 <__printf_chk@plt>
    4bcb:	ba 02 00 00 00       	mov    $0x2,%edx
    4bd0:	48 8d 35 89 c6 00 00 	lea    0xc689(%rip),%rsi        # 11260 <_IO_stdin_used+0x1260>
    4bd7:	31 c0                	xor    %eax,%eax
    4bd9:	bf 01 00 00 00       	mov    $0x1,%edi
    4bde:	e8 3d f9 ff ff       	call   4520 <__printf_chk@plt>
    4be3:	ba 01 00 00 00       	mov    $0x1,%edx
    4be8:	48 8d 35 b1 c6 00 00 	lea    0xc6b1(%rip),%rsi        # 112a0 <_IO_stdin_used+0x12a0>
    4bef:	31 c0                	xor    %eax,%eax
    4bf1:	bf 01 00 00 00       	mov    $0x1,%edi
    4bf6:	e8 25 f9 ff ff       	call   4520 <__printf_chk@plt>
    4bfb:	ba 01 00 00 00       	mov    $0x1,%edx
    4c00:	48 8d 35 f9 c6 00 00 	lea    0xc6f9(%rip),%rsi        # 11300 <_IO_stdin_used+0x1300>
    4c07:	31 c0                	xor    %eax,%eax
    4c09:	bf 01 00 00 00       	mov    $0x1,%edi
    4c0e:	e8 0d f9 ff ff       	call   4520 <__printf_chk@plt>
    4c13:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    4c18:	48 8d 35 41 c7 00 00 	lea    0xc741(%rip),%rsi        # 11360 <_IO_stdin_used+0x1360>
    4c1f:	31 c0                	xor    %eax,%eax
    4c21:	bf 01 00 00 00       	mov    $0x1,%edi
    4c26:	e8 f5 f8 ff ff       	call   4520 <__printf_chk@plt>
    4c2b:	ba 05 00 00 00       	mov    $0x5,%edx
    4c30:	48 8d 35 69 c7 00 00 	lea    0xc769(%rip),%rsi        # 113a0 <_IO_stdin_used+0x13a0>
    4c37:	31 c0                	xor    %eax,%eax
    4c39:	bf 01 00 00 00       	mov    $0x1,%edi
    4c3e:	e8 dd f8 ff ff       	call   4520 <__printf_chk@plt>
    4c43:	48 8d 3d 96 c7 00 00 	lea    0xc796(%rip),%rdi        # 113e0 <_IO_stdin_used+0x13e0>
    4c4a:	e8 b1 fb ff ff       	call   4800 <puts@plt>
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    4c4f:	be 18 00 00 00       	mov    $0x18,%esi
    4c54:	bf 06 00 00 00       	mov    $0x6,%edi
    4c59:	e8 02 f8 ff ff       	call   4460 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    4c5e:	be c0 00 00 00       	mov    $0xc0,%esi
    4c63:	bf 10 00 00 00       	mov    $0x10,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    4c68:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    4c70:	e8 eb f7 ff ff       	call   4460 <calloc@plt>
    4c75:	ba 0c 00 00 00       	mov    $0xc,%edx
    4c7a:	bf 01 00 00 00       	mov    $0x1,%edi
    4c7f:	48 8d 35 9a c7 00 00 	lea    0xc79a(%rip),%rsi        # 11420 <_IO_stdin_used+0x1420>
    4c86:	48 89 04 24          	mov    %rax,(%rsp)
    4c8a:	31 c0                	xor    %eax,%eax
    4c8c:	e8 8f f8 ff ff       	call   4520 <__printf_chk@plt>
    4c91:	ba 18 00 00 00       	mov    $0x18,%edx
    4c96:	48 8d 35 c3 c7 00 00 	lea    0xc7c3(%rip),%rsi        # 11460 <_IO_stdin_used+0x1460>
    4c9d:	31 c0                	xor    %eax,%eax
    4c9f:	bf 01 00 00 00       	mov    $0x1,%edi
    4ca4:	e8 77 f8 ff ff       	call   4520 <__printf_chk@plt>
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    4ca9:	be 10 00 00 00       	mov    $0x10,%esi
    4cae:	bf 18 00 00 00       	mov    $0x18,%edi
    4cb3:	e8 a8 f7 ff ff       	call   4460 <calloc@plt>
    4cb8:	4c 8b 24 24          	mov    (%rsp),%r12
    4cbc:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
    4cc4:	49 89 c5             	mov    %rax,%r13
    4cc7:	48 8d 98 80 01 00 00 	lea    0x180(%rax),%rbx
    4cce:	48 89 84 24 a0 00 00 00 	mov    %rax,0xa0(%rsp)
    4cd6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    buffers[x].count = buffer_size;
    4ce0:	4c 89 e8             	mov    %r13,%rax
    4ce3:	48 c1 e8 03          	shr    $0x3,%rax
    4ce7:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    4cee:	84 c0                	test   %al,%al
    4cf0:	74 08                	je     4cfa <main+0x26a>
    4cf2:	3c 03                	cmp    $0x3,%al
    4cf4:	0f 8e 2f 29 00 00    	jle    7629 <main+0x2b99>
    4cfa:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    4d02:	bf 01 00 00 00       	mov    $0x1,%edi
    4d07:	be 00 01 00 00       	mov    $0x100,%esi
    4d0c:	e8 4f f7 ff ff       	call   4460 <calloc@plt>
    4d11:	49 8d 7d 08          	lea    0x8(%r13),%rdi
    4d15:	48 89 c5             	mov    %rax,%rbp
    4d18:	48 89 f8             	mov    %rdi,%rax
    4d1b:	48 c1 e8 03          	shr    $0x3,%rax
    4d1f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    4d26:	0f 85 f8 28 00 00    	jne    7624 <main+0x2b94>
      buffers[x].buffer[y].available = 0;
    4d2c:	48 8d bd 80 00 00 00 	lea    0x80(%rbp),%rdi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    4d33:	49 89 6d 08          	mov    %rbp,0x8(%r13)
      buffers[x].buffer[y].available = 0;
    4d37:	48 89 f8             	mov    %rdi,%rax
    4d3a:	48 c1 e8 03          	shr    $0x3,%rax
    4d3e:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    4d45:	84 c0                	test   %al,%al
    4d47:	74 08                	je     4d51 <main+0x2c1>
    4d49:	3c 03                	cmp    $0x3,%al
    4d4b:	0f 8e 2e 29 00 00    	jle    767f <main+0x2bef>
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    4d51:	48 8d bd 90 00 00 00 	lea    0x90(%rbp),%rdi
      buffers[x].buffer[y].available = 0;
    4d58:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    4d62:	48 89 f8             	mov    %rdi,%rax
    4d65:	48 c1 e8 03          	shr    $0x3,%rax
    4d69:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    4d70:	84 c0                	test   %al,%al
    4d72:	74 08                	je     4d7c <main+0x2ec>
    4d74:	3c 03                	cmp    $0x3,%al
    4d76:	0f 8e fe 28 00 00    	jle    767a <main+0x2bea>
    4d7c:	c7 85 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rbp)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    4d86:	bf 64 00 00 00       	mov    $0x64,%edi
    4d8b:	be 20 00 00 00       	mov    $0x20,%esi
    4d90:	e8 cb f6 ff ff       	call   4460 <calloc@plt>
    4d95:	48 8d bd 88 00 00 00 	lea    0x88(%rbp),%rdi
    4d9c:	48 89 fa             	mov    %rdi,%rdx
    4d9f:	48 c1 ea 03          	shr    $0x3,%rdx
    4da3:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    4daa:	0f 85 c5 28 00 00    	jne    7675 <main+0x2be5>
  for (int x = 0 ; x < buffers_required; x++) {
    4db0:	49 83 c5 10          	add    $0x10,%r13
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    4db4:	48 89 85 88 00 00 00 	mov    %rax,0x88(%rbp)
  for (int x = 0 ; x < buffers_required; x++) {
    4dbb:	49 39 dd             	cmp    %rbx,%r13
    4dbe:	0f 85 1c ff ff ff    	jne    4ce0 <main+0x250>
    4dc4:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
  int curcpu = 0;
    4dcc:	c7 44 24 50 00 00 00 00 	movl   $0x0,0x50(%rsp)
  for (int x = 0 ; x < buffers_required; x++) {
    4dd4:	45 31 c9             	xor    %r9d,%r9d
  int cur_buffer = 0;
    4dd7:	31 d2                	xor    %edx,%edx
    4dd9:	4c 89 64 24 48       	mov    %r12,0x48(%rsp)
    4dde:	48 89 84 24 80 00 00 00 	mov    %rax,0x80(%rsp)
  for (int x = 0 ; x < buffers_required; x++) {
    4de6:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    4deb:	48 8b 5c 24 48       	mov    0x48(%rsp),%rbx
    4df0:	4b 8d 04 49          	lea    (%r9,%r9,2),%rax
    4df4:	43 8d 2c 09          	lea    (%r9,%r9,1),%ebp
    4df8:	44 89 4c 24 68       	mov    %r9d,0x68(%rsp)
    for (int d = 0 ; d < threads_per_group ; d++) {
    4dfd:	48 c1 e0 07          	shl    $0x7,%rax
    4e01:	4c 89 4c 24 70       	mov    %r9,0x70(%rsp)
    4e06:	44 8d 75 01          	lea    0x1(%rbp),%r14d
    4e0a:	4c 8d 14 18          	lea    (%rax,%rbx,1),%r10
    4e0e:	48 63 c2             	movslq %edx,%rax
    4e11:	48 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%rbx
    4e19:	29 ea                	sub    %ebp,%edx
    4e1b:	48 c1 e0 04          	shl    $0x4,%rax
    4e1f:	89 54 24 7c          	mov    %edx,0x7c(%rsp)
    4e23:	48 01 d8             	add    %rbx,%rax
    4e26:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    4e2b:	8d 45 03             	lea    0x3(%rbp),%eax
    4e2e:	89 44 24 58          	mov    %eax,0x58(%rsp)
    4e32:	8b 54 24 68          	mov    0x68(%rsp),%edx
    4e36:	89 e9                	mov    %ebp,%ecx
    4e38:	48 8d 35 61 c6 00 00 	lea    0xc661(%rip),%rsi        # 114a0 <_IO_stdin_used+0x14a0>
    4e3f:	31 c0                	xor    %eax,%eax
    4e41:	bf 01 00 00 00       	mov    $0x1,%edi
    4e46:	4c 89 14 24          	mov    %r10,(%rsp)
    4e4a:	e8 d1 f6 ff ff       	call   4520 <__printf_chk@plt>
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    4e4f:	be 08 00 00 00       	mov    $0x8,%esi
    4e54:	bf 02 00 00 00       	mov    $0x2,%edi
    4e59:	e8 02 f6 ff ff       	call   4460 <calloc@plt>
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    4e5e:	be 80 00 00 00       	mov    $0x80,%esi
    4e63:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    4e68:	49 89 c4             	mov    %rax,%r12
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    4e6b:	e8 f0 f5 ff ff       	call   4460 <calloc@plt>
      if (x % 2 == 1) {
    4e70:	40 f6 c5 01          	test   $0x1,%bpl
    4e74:	4c 8b 14 24          	mov    (%rsp),%r10
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    4e78:	49 89 c7             	mov    %rax,%r15
      if (x % 2 == 1) {
    4e7b:	0f 84 73 0f 00 00    	je     5df4 <main+0x1364>
        other = abs(x - 1) % total_threads;
    4e81:	8d 45 ff             	lea    -0x1(%rbp),%eax
        my_thread_data[0] = &thread_data[other]; 
    4e84:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
        my_thread_data[1] = &thread_data[x]; 
    4e89:	4c 89 d2             	mov    %r10,%rdx
    4e8c:	41 b8 01 00 00 00    	mov    $0x1,%r8d
        other = abs(x - 1) % total_threads;
    4e92:	48 89 c3             	mov    %rax,%rbx
        my_thread_data[0] = &thread_data[other]; 
    4e95:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    4e99:	48 c1 e0 06          	shl    $0x6,%rax
    4e9d:	48 01 f0             	add    %rsi,%rax
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    4ea0:	49 8d 74 24 08       	lea    0x8(%r12),%rsi
    4ea5:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
        thread_data[x].thread_index = 1;
    4eaa:	49 8d 7a 04          	lea    0x4(%r10),%rdi
    4eae:	48 89 f9             	mov    %rdi,%rcx
    4eb1:	48 89 7c 24 30       	mov    %rdi,0x30(%rsp)
    4eb6:	48 c1 e9 03          	shr    $0x3,%rcx
    4eba:	0f b6 b1 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%esi
    4ec1:	48 89 f9             	mov    %rdi,%rcx
    4ec4:	83 e1 07             	and    $0x7,%ecx
    4ec7:	83 c1 03             	add    $0x3,%ecx
    4eca:	40 38 f1             	cmp    %sil,%cl
    4ecd:	7c 09                	jl     4ed8 <main+0x448>
    4ecf:	40 84 f6             	test   %sil,%sil
    4ed2:	0f 85 98 27 00 00    	jne    7670 <main+0x2be0>
        thread_data[x].protected_state = &protected_state[k];
    4ed8:	49 8d 7a 48          	lea    0x48(%r10),%rdi
        thread_data[x].thread_index = 1;
    4edc:	45 89 42 04          	mov    %r8d,0x4(%r10)
        thread_data[x].protected_state = &protected_state[k];
    4ee0:	48 89 f9             	mov    %rdi,%rcx
    4ee3:	48 c1 e9 03          	shr    $0x3,%rcx
    4ee7:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    4eee:	0f 85 77 27 00 00    	jne    766b <main+0x2bdb>
        my_thread_data[1] = &thread_data[x]; 
    4ef4:	49 8d 7c 24 08       	lea    0x8(%r12),%rdi
        thread_data[x].protected_state = &protected_state[k];
    4ef9:	48 8b 74 24 60       	mov    0x60(%rsp),%rsi
        my_thread_data[1] = &thread_data[x]; 
    4efe:	48 89 f9             	mov    %rdi,%rcx
    4f01:	48 c1 e9 03          	shr    $0x3,%rcx
        thread_data[x].protected_state = &protected_state[k];
    4f05:	49 89 72 48          	mov    %rsi,0x48(%r10)
        my_thread_data[1] = &thread_data[x]; 
    4f09:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    4f10:	0f 85 50 27 00 00    	jne    7666 <main+0x2bd6>
    4f16:	49 89 54 24 08       	mov    %rdx,0x8(%r12)
        my_thread_data[0] = &thread_data[other]; 
    4f1b:	4c 89 e2             	mov    %r12,%rdx
    4f1e:	48 c1 ea 03          	shr    $0x3,%rdx
    4f22:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    4f29:	0f 85 2f 27 00 00    	jne    765e <main+0x2bce>
    4f2f:	49 89 04 24          	mov    %rax,(%r12)
    4f33:	bf 01 00 00 00       	mov    $0x1,%edi
    4f38:	89 d9                	mov    %ebx,%ecx
    4f3a:	89 ea                	mov    %ebp,%edx
    4f3c:	48 8d 35 bd c5 00 00 	lea    0xc5bd(%rip),%rsi        # 11500 <_IO_stdin_used+0x1500>
    4f43:	31 c0                	xor    %eax,%eax
    4f45:	4c 89 14 24          	mov    %r10,(%rsp)
    4f49:	e8 d2 f5 ff ff       	call   4520 <__printf_chk@plt>
      thread_data[x].other = other;
    4f4e:	4c 8b 14 24          	mov    (%rsp),%r10
    4f52:	49 8d ba b8 00 00 00 	lea    0xb8(%r10),%rdi
    4f59:	48 89 f8             	mov    %rdi,%rax
    4f5c:	48 c1 e8 03          	shr    $0x3,%rax
    4f60:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    4f67:	84 c0                	test   %al,%al
    4f69:	74 08                	je     4f73 <main+0x4e3>
    4f6b:	3c 03                	cmp    $0x3,%al
    4f6d:	0f 8e e6 26 00 00    	jle    7659 <main+0x2bc9>
    4f73:	41 89 9a b8 00 00 00 	mov    %ebx,0xb8(%r10)
    4f7a:	8b 4c 24 50          	mov    0x50(%rsp),%ecx
    4f7e:	31 c0                	xor    %eax,%eax
    4f80:	89 ea                	mov    %ebp,%edx
    4f82:	48 8d 35 d7 c5 00 00 	lea    0xc5d7(%rip),%rsi        # 11560 <_IO_stdin_used+0x1560>
    4f89:	bf 01 00 00 00       	mov    $0x1,%edi
    4f8e:	4c 89 14 24          	mov    %r10,(%rsp)
    4f92:	e8 89 f5 ff ff       	call   4520 <__printf_chk@plt>
        if (x < thread_count) {
    4f97:	83 fd 01             	cmp    $0x1,%ebp
    4f9a:	4c 8b 14 24          	mov    (%rsp),%r10
    4f9e:	0f 8f 76 0e 00 00    	jg     5e1a <main+0x138a>
          CPU_SET(curcpu, sendercpu);
    4fa4:	48 63 44 24 50       	movslq 0x50(%rsp),%rax
    4fa9:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    4faf:	77 2c                	ja     4fdd <main+0x54d>
    4fb1:	48 c1 e8 06          	shr    $0x6,%rax
    4fb5:	49 8d 3c c7          	lea    (%r15,%rax,8),%rdi
    4fb9:	48 89 f8             	mov    %rdi,%rax
    4fbc:	48 c1 e8 03          	shr    $0x3,%rax
    4fc0:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    4fc7:	0f 85 15 27 00 00    	jne    76e2 <main+0x2c52>
    4fcd:	0f b6 4c 24 50       	movzbl 0x50(%rsp),%ecx
    4fd2:	b8 01 00 00 00       	mov    $0x1,%eax
    4fd7:	48 d3 e0             	shl    %cl,%rax
    4fda:	48 09 07             	or     %rax,(%rdi)
          curcpu += 2;
    4fdd:	83 44 24 50 02       	addl   $0x2,0x50(%rsp)
      thread_data[x].kind = KERNEL_THREAD;
    4fe2:	4c 89 d0             	mov    %r10,%rax
    4fe5:	48 c1 e8 03          	shr    $0x3,%rax
    4fe9:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    4ff0:	84 c0                	test   %al,%al
    4ff2:	74 08                	je     4ffc <main+0x56c>
    4ff4:	3c 03                	cmp    $0x3,%al
    4ff6:	0f 8e de 26 00 00    	jle    76da <main+0x2c4a>
      thread_data[x].cpu_set = sendercpu;
    4ffc:	49 8d ba b0 00 00 00 	lea    0xb0(%r10),%rdi
      thread_data[x].kind = KERNEL_THREAD;
    5003:	41 c7 02 5f 00 00 00 	movl   $0x5f,(%r10)
      thread_data[x].cpu_set = sendercpu;
    500a:	48 89 f8             	mov    %rdi,%rax
    500d:	48 c1 e8 03          	shr    $0x3,%rax
    5011:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5018:	0f 85 b7 26 00 00    	jne    76d5 <main+0x2c45>
      thread_data[x].real_thread_index = x;
    501e:	49 8d 7a 08          	lea    0x8(%r10),%rdi
      thread_data[x].cpu_set = sendercpu;
    5022:	4d 89 ba b0 00 00 00 	mov    %r15,0xb0(%r10)
      thread_data[x].real_thread_index = x;
    5029:	48 89 f8             	mov    %rdi,%rax
    502c:	48 c1 e8 03          	shr    $0x3,%rax
    5030:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    5037:	84 c0                	test   %al,%al
    5039:	74 08                	je     5043 <main+0x5b3>
    503b:	3c 03                	cmp    $0x3,%al
    503d:	0f 8e 8d 26 00 00    	jle    76d0 <main+0x2c40>
      thread_data[x].threads = my_thread_data;
    5043:	49 8d 7a 18          	lea    0x18(%r10),%rdi
      thread_data[x].real_thread_index = x;
    5047:	41 89 6a 08          	mov    %ebp,0x8(%r10)
      thread_data[x].threads = my_thread_data;
    504b:	48 89 f8             	mov    %rdi,%rax
    504e:	48 c1 e8 03          	shr    $0x3,%rax
    5052:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5059:	0f 85 6c 26 00 00    	jne    76cb <main+0x2c3b>
      thread_data[x].all_threads = thread_data;
    505f:	49 8d 7a 20          	lea    0x20(%r10),%rdi
      thread_data[x].threads = my_thread_data;
    5063:	4d 89 62 18          	mov    %r12,0x18(%r10)
      thread_data[x].all_threads = thread_data;
    5067:	48 89 f8             	mov    %rdi,%rax
    506a:	48 c1 e8 03          	shr    $0x3,%rax
    506e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5075:	0f 85 4b 26 00 00    	jne    76c6 <main+0x2c36>
    507b:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
      thread_data[x].thread_count = 2;
    5080:	49 8d 7a 28          	lea    0x28(%r10),%rdi
      thread_data[x].all_threads = thread_data;
    5084:	49 89 42 20          	mov    %rax,0x20(%r10)
      thread_data[x].thread_count = 2;
    5088:	48 89 f8             	mov    %rdi,%rax
    508b:	48 c1 e8 03          	shr    $0x3,%rax
    508f:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    5096:	84 c0                	test   %al,%al
    5098:	74 08                	je     50a2 <main+0x612>
    509a:	3c 03                	cmp    $0x3,%al
    509c:	0f 8e 1f 26 00 00    	jle    76c1 <main+0x2c31>
      thread_data[x].total_thread_count = total_threads;
    50a2:	49 8d 7a 2c          	lea    0x2c(%r10),%rdi
      thread_data[x].thread_count = 2;
    50a6:	41 c7 42 28 02 00 00 00 	movl   $0x2,0x28(%r10)
      thread_data[x].total_thread_count = total_threads;
    50ae:	48 89 f8             	mov    %rdi,%rax
    50b1:	48 c1 e8 03          	shr    $0x3,%rax
    50b5:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    50bc:	48 89 f8             	mov    %rdi,%rax
    50bf:	83 e0 07             	and    $0x7,%eax
    50c2:	83 c0 03             	add    $0x3,%eax
    50c5:	38 d0                	cmp    %dl,%al
    50c7:	7c 08                	jl     50d1 <main+0x641>
    50c9:	84 d2                	test   %dl,%dl
    50cb:	0f 85 eb 25 00 00    	jne    76bc <main+0x2c2c>
      thread_data[x].task_count = total_barrier_count;
    50d1:	49 8d 7a 40          	lea    0x40(%r10),%rdi
      thread_data[x].total_thread_count = total_threads;
    50d5:	41 c7 42 2c 10 00 00 00 	movl   $0x10,0x2c(%r10)
      thread_data[x].task_count = total_barrier_count;
    50dd:	48 89 f8             	mov    %rdi,%rax
    50e0:	48 c1 e8 03          	shr    $0x3,%rax
    50e4:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    50eb:	84 c0                	test   %al,%al
    50ed:	74 08                	je     50f7 <main+0x667>
    50ef:	3c 03                	cmp    $0x3,%al
    50f1:	0f 8e c0 25 00 00    	jle    76b7 <main+0x2c27>
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    50f7:	bf 64 00 00 00       	mov    $0x64,%edi
    50fc:	be 10 00 00 00       	mov    $0x10,%esi
      thread_data[x].task_count = total_barrier_count;
    5101:	41 c7 42 40 03 00 00 00 	movl   $0x3,0x40(%r10)
    5109:	4c 89 14 24          	mov    %r10,(%rsp)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    510d:	e8 4e f3 ff ff       	call   4460 <calloc@plt>
    5112:	4c 8b 14 24          	mov    (%rsp),%r10
    5116:	49 8d 7a 68          	lea    0x68(%r10),%rdi
    511a:	48 89 fa             	mov    %rdi,%rdx
    511d:	48 c1 ea 03          	shr    $0x3,%rdx
    5121:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    5128:	0f 85 75 26 00 00    	jne    77a3 <main+0x2d13>
    512e:	49 89 42 68          	mov    %rax,0x68(%r10)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    5132:	bf 64 00 00 00       	mov    $0x64,%edi
    5137:	be 10 00 00 00       	mov    $0x10,%esi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    513c:	4c 89 14 24          	mov    %r10,(%rsp)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    5140:	e8 1b f3 ff ff       	call   4460 <calloc@plt>
    5145:	4c 8b 14 24          	mov    (%rsp),%r10
    5149:	49 8d 7a 70          	lea    0x70(%r10),%rdi
    514d:	48 89 fa             	mov    %rdi,%rdx
    5150:	48 c1 ea 03          	shr    $0x3,%rdx
    5154:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    515b:	0f 85 3d 26 00 00    	jne    779e <main+0x2d0e>
      thread_data[x].timestamp_count = 0;
    5161:	49 8d ba 80 00 00 00 	lea    0x80(%r10),%rdi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    5168:	49 89 42 70          	mov    %rax,0x70(%r10)
      thread_data[x].timestamp_count = 0;
    516c:	48 89 f8             	mov    %rdi,%rax
    516f:	48 c1 e8 03          	shr    $0x3,%rax
    5173:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    517a:	0f 85 19 26 00 00    	jne    7799 <main+0x2d09>
      thread_data[x].timestamp_limit = timestamp_limit;
    5180:	49 8d ba 88 00 00 00 	lea    0x88(%r10),%rdi
      thread_data[x].timestamp_count = 0;
    5187:	49 c7 82 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%r10)
      thread_data[x].timestamp_limit = timestamp_limit;
    5192:	48 89 f8             	mov    %rdi,%rax
    5195:	48 c1 e8 03          	shr    $0x3,%rax
    5199:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    51a0:	0f 85 ee 25 00 00    	jne    7794 <main+0x2d04>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    51a6:	bf 64 00 00 00       	mov    $0x64,%edi
    51ab:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_limit = timestamp_limit;
    51b0:	4c 89 14 24          	mov    %r10,(%rsp)
    51b4:	49 c7 82 88 00 00 00 64 00 00 00 	movq   $0x64,0x88(%r10)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    51bf:	e8 9c f2 ff ff       	call   4460 <calloc@plt>
    51c4:	4c 8b 14 24          	mov    (%rsp),%r10
    51c8:	49 8d ba 90 00 00 00 	lea    0x90(%r10),%rdi
    51cf:	48 89 fa             	mov    %rdi,%rdx
    51d2:	48 c1 ea 03          	shr    $0x3,%rdx
    51d6:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    51dd:	0f 85 ac 25 00 00    	jne    778f <main+0x2cff>
      thread_data[x].task_timestamp_count = 0;
    51e3:	49 8d ba 98 00 00 00 	lea    0x98(%r10),%rdi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    51ea:	49 89 82 90 00 00 00 	mov    %rax,0x90(%r10)
      thread_data[x].task_timestamp_count = 0;
    51f1:	48 89 f8             	mov    %rdi,%rax
    51f4:	48 c1 e8 03          	shr    $0x3,%rax
    51f8:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    51ff:	0f 85 85 25 00 00    	jne    778a <main+0x2cfa>
      thread_data[x].task_timestamp_limit = timestamp_limit;
    5205:	49 8d ba a0 00 00 00 	lea    0xa0(%r10),%rdi
      thread_data[x].task_timestamp_count = 0;
    520c:	49 c7 82 98 00 00 00 00 00 00 00 	movq   $0x0,0x98(%r10)
      thread_data[x].task_timestamp_limit = timestamp_limit;
    5217:	48 89 f8             	mov    %rdi,%rax
    521a:	48 c1 e8 03          	shr    $0x3,%rax
    521e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5225:	0f 85 5a 25 00 00    	jne    7785 <main+0x2cf5>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    522b:	be 00 02 00 00       	mov    $0x200,%esi
    5230:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_limit = timestamp_limit;
    5235:	4c 89 14 24          	mov    %r10,(%rsp)
    5239:	49 c7 82 a0 00 00 00 64 00 00 00 	movq   $0x64,0xa0(%r10)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    5244:	e8 17 f2 ff ff       	call   4460 <calloc@plt>
        thread_data[x].tasks = barriers;
    5249:	4c 8b 14 24          	mov    (%rsp),%r10
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    524d:	49 89 c7             	mov    %rax,%r15
        thread_data[x].tasks = barriers;
    5250:	4d 8d 4a 38          	lea    0x38(%r10),%r9
    5254:	4c 89 c8             	mov    %r9,%rax
    5257:	48 c1 e8 03          	shr    $0x3,%rax
    525b:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5262:	0f 85 15 25 00 00    	jne    777d <main+0x2ced>
    5268:	4d 89 7a 38          	mov    %r15,0x38(%r10)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    526c:	45 31 e4             	xor    %r12d,%r12d
    526f:	4c 89 fa             	mov    %r15,%rdx
    5272:	4c 89 4c 24 38       	mov    %r9,0x38(%rsp)
    5277:	4c 89 14 24          	mov    %r10,(%rsp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    527b:	49 63 c4             	movslq %r12d,%rax
    527e:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    5283:	48 c1 e0 09          	shl    $0x9,%rax
    5287:	4c 8d 2c 02          	lea    (%rdx,%rax,1),%r13
    528b:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5290:	49 8d bd 20 01 00 00 	lea    0x120(%r13),%rdi
    5297:	48 89 f8             	mov    %rdi,%rax
    529a:	48 c1 e8 03          	shr    $0x3,%rax
    529e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    52a5:	0f 85 8d 26 00 00    	jne    7938 <main+0x2ea8>
    52ab:	48 8d 05 be 27 00 00 	lea    0x27be(%rip),%rax        # 7a70 <do_protected_write>
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    52b2:	bf 0c 00 00 00       	mov    $0xc,%edi
    52b7:	be 28 00 00 00       	mov    $0x28,%esi
          thread_data[x].tasks[y].protected = do_protected_write; 
    52bc:	49 89 85 20 01 00 00 	mov    %rax,0x120(%r13)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    52c3:	e8 98 f1 ff ff       	call   4460 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    52c8:	49 8d bd 70 01 00 00 	lea    0x170(%r13),%rdi
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    52cf:	48 89 c3             	mov    %rax,%rbx
          thread_data[x].tasks[y].mailboxes = mailboxes;
    52d2:	48 89 f8             	mov    %rdi,%rax
    52d5:	48 c1 e8 03          	shr    $0x3,%rax
    52d9:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    52e0:	0f 85 45 26 00 00    	jne    792b <main+0x2e9b>
    52e6:	49 89 9d 70 01 00 00 	mov    %rbx,0x170(%r13)
    52ed:	49 89 df             	mov    %rbx,%r15
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    52f0:	45 31 ed             	xor    %r13d,%r13d
    52f3:	44 89 64 24 20       	mov    %r12d,0x20(%rsp)
    52f8:	45 89 f4             	mov    %r14d,%r12d
    52fb:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    5300:	eb 18                	jmp    531a <main+0x88a>
    5302:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5308:	41 83 c5 01          	add    $0x1,%r13d
    530c:	49 83 c7 28          	add    $0x28,%r15
    5310:	41 83 fd 0c          	cmp    $0xc,%r13d
    5314:	0f 84 75 01 00 00    	je     548f <main+0x9ff>
            if ( b == x || b == x + 1) {
    531a:	41 39 ed             	cmp    %ebp,%r13d
    531d:	74 05                	je     5324 <main+0x894>
    531f:	45 39 e5             	cmp    %r12d,%r13d
    5322:	75 e4                	jne    5308 <main+0x878>
    5324:	44 89 ea             	mov    %r13d,%edx
    5327:	48 8d 35 72 c2 00 00 	lea    0xc272(%rip),%rsi        # 115a0 <_IO_stdin_used+0x15a0>
    532e:	bf 01 00 00 00       	mov    $0x1,%edi
    5333:	31 c0                	xor    %eax,%eax
    5335:	e8 e6 f1 ff ff       	call   4520 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    533a:	be 08 00 00 00       	mov    $0x8,%esi
    533f:	bf 01 00 00 00       	mov    $0x1,%edi
    5344:	e8 17 f1 ff ff       	call   4460 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    5349:	be 08 00 00 00       	mov    $0x8,%esi
    534e:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    5353:	49 89 c6             	mov    %rax,%r14
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    5356:	e8 05 f1 ff ff       	call   4460 <calloc@plt>
              struct Data *data = calloc(2, sizeof(struct Data));
    535b:	bf 02 00 00 00       	mov    $0x2,%edi
    5360:	be 20 00 00 00       	mov    $0x20,%esi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    5365:	48 89 c3             	mov    %rax,%rbx
              struct Data *data = calloc(2, sizeof(struct Data));
    5368:	e8 f3 f0 ff ff       	call   4460 <calloc@plt>
    536d:	48 89 c7             	mov    %rax,%rdi
              mailboxes[b].lower = &data[0];
    5370:	4c 89 f8             	mov    %r15,%rax
    5373:	48 c1 e8 03          	shr    $0x3,%rax
    5377:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    537e:	0f 85 b8 20 00 00    	jne    743c <main+0x29ac>
              mailboxes[b].higher = &data[1];
    5384:	49 8d 77 08          	lea    0x8(%r15),%rsi
              mailboxes[b].lower = &data[0];
    5388:	49 89 3f             	mov    %rdi,(%r15)
              mailboxes[b].higher = &data[1];
    538b:	48 8d 47 20          	lea    0x20(%rdi),%rax
    538f:	48 89 f2             	mov    %rsi,%rdx
    5392:	48 c1 ea 03          	shr    $0x3,%rdx
    5396:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    539d:	0f 85 a1 20 00 00    	jne    7444 <main+0x29b4>
              mailboxes[b].kind = MAILBOX_FRIEND;
    53a3:	4d 8d 47 20          	lea    0x20(%r15),%r8
              mailboxes[b].higher = &data[1];
    53a7:	49 89 47 08          	mov    %rax,0x8(%r15)
              mailboxes[b].kind = MAILBOX_FRIEND;
    53ab:	4c 89 c2             	mov    %r8,%rdx
    53ae:	48 c1 ea 03          	shr    $0x3,%rdx
    53b2:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    53b9:	84 d2                	test   %dl,%dl
    53bb:	74 09                	je     53c6 <main+0x936>
    53bd:	80 fa 03             	cmp    $0x3,%dl
    53c0:	0f 8e 86 20 00 00    	jle    744c <main+0x29bc>
              data[0].messages = messages;
    53c6:	48 89 fa             	mov    %rdi,%rdx
              mailboxes[b].kind = MAILBOX_FRIEND;
    53c9:	41 c7 47 20 01 00 00 00 	movl   $0x1,0x20(%r15)
              data[0].messages = messages;
    53d1:	48 c1 ea 03          	shr    $0x3,%rdx
    53d5:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    53dc:	0f 85 72 20 00 00    	jne    7454 <main+0x29c4>
              data[1].messages = messages2;
    53e2:	48 89 c2             	mov    %rax,%rdx
              data[0].messages = messages;
    53e5:	4c 89 37             	mov    %r14,(%rdi)
              data[1].messages = messages2;
    53e8:	48 c1 ea 03          	shr    $0x3,%rdx
    53ec:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    53f3:	0f 85 60 20 00 00    	jne    7459 <main+0x29c9>
              data[0].messages_limit = messages_limit;
    53f9:	48 8d 47 10          	lea    0x10(%rdi),%rax
              data[1].messages = messages2;
    53fd:	48 89 5f 20          	mov    %rbx,0x20(%rdi)
              data[0].messages_limit = messages_limit;
    5401:	48 89 c2             	mov    %rax,%rdx
    5404:	48 c1 ea 03          	shr    $0x3,%rdx
    5408:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    540f:	0f 85 4c 20 00 00    	jne    7461 <main+0x29d1>
              data[0].messages_count = 0;
    5415:	48 8d 47 08          	lea    0x8(%rdi),%rax
              data[0].messages_limit = messages_limit;
    5419:	48 c7 47 10 01 00 00 00 	movq   $0x1,0x10(%rdi)
              data[0].messages_count = 0;
    5421:	48 89 c2             	mov    %rax,%rdx
    5424:	48 c1 ea 03          	shr    $0x3,%rdx
    5428:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    542f:	0f 85 34 20 00 00    	jne    7469 <main+0x29d9>
              data[1].messages_count = 0;
    5435:	48 8d 47 28          	lea    0x28(%rdi),%rax
              data[0].messages_count = 0;
    5439:	48 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%rdi)
              data[1].messages_count = 0;
    5441:	48 89 c2             	mov    %rax,%rdx
    5444:	48 c1 ea 03          	shr    $0x3,%rdx
    5448:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    544f:	0f 85 1c 20 00 00    	jne    7471 <main+0x29e1>
              data[1].messages_limit = messages_limit;
    5455:	48 8d 47 30          	lea    0x30(%rdi),%rax
              data[1].messages_count = 0;
    5459:	48 c7 47 28 00 00 00 00 	movq   $0x0,0x28(%rdi)
              data[1].messages_limit = messages_limit;
    5461:	48 89 c2             	mov    %rax,%rdx
    5464:	48 c1 ea 03          	shr    $0x3,%rdx
    5468:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    546f:	0f 85 04 20 00 00    	jne    7479 <main+0x29e9>
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    5475:	41 83 c5 01          	add    $0x1,%r13d
              data[1].messages_limit = messages_limit;
    5479:	48 c7 47 30 01 00 00 00 	movq   $0x1,0x30(%rdi)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    5481:	49 83 c7 28          	add    $0x28,%r15
    5485:	41 83 fd 0c          	cmp    $0xc,%r13d
    5489:	0f 85 8b fe ff ff    	jne    531a <main+0x88a>
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    548f:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    5494:	45 89 e6             	mov    %r12d,%r14d
    5497:	45 31 ff             	xor    %r15d,%r15d
    549a:	41 89 ec             	mov    %ebp,%r12d
    549d:	0f 1f 00             	nopl   (%rax)
            if (b == x || b == x + 1) { continue; }
    54a0:	45 39 e7             	cmp    %r12d,%r15d
    54a3:	0f 84 ac 01 00 00    	je     5655 <main+0xbc5>
    54a9:	45 39 f7             	cmp    %r14d,%r15d
    54ac:	0f 84 a3 01 00 00    	je     5655 <main+0xbc5>
    54b2:	44 89 fa             	mov    %r15d,%edx
    54b5:	48 8d 35 24 c1 00 00 	lea    0xc124(%rip),%rsi        # 115e0 <_IO_stdin_used+0x15e0>
    54bc:	bf 01 00 00 00       	mov    $0x1,%edi
    54c1:	31 c0                	xor    %eax,%eax
    54c3:	e8 58 f0 ff ff       	call   4520 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    54c8:	be 08 00 00 00       	mov    $0x8,%esi
    54cd:	bf 01 00 00 00       	mov    $0x1,%edi
    54d2:	e8 89 ef ff ff       	call   4460 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    54d7:	be 08 00 00 00       	mov    $0x8,%esi
    54dc:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    54e1:	48 89 c5             	mov    %rax,%rbp
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    54e4:	e8 77 ef ff ff       	call   4460 <calloc@plt>
            struct Data *data = calloc(2, sizeof(struct Data));
    54e9:	bf 02 00 00 00       	mov    $0x2,%edi
    54ee:	be 20 00 00 00       	mov    $0x20,%esi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    54f3:	49 89 c5             	mov    %rax,%r13
            struct Data *data = calloc(2, sizeof(struct Data));
    54f6:	e8 65 ef ff ff       	call   4460 <calloc@plt>
    54fb:	48 89 c7             	mov    %rax,%rdi
            mailboxes[b].lower = &data[0];
    54fe:	48 89 d8             	mov    %rbx,%rax
    5501:	48 c1 e8 03          	shr    $0x3,%rax
    5505:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    550c:	0f 85 6f 1f 00 00    	jne    7481 <main+0x29f1>
            mailboxes[b].higher = &data[1];
    5512:	48 8d 4b 08          	lea    0x8(%rbx),%rcx
            mailboxes[b].lower = &data[0];
    5516:	48 89 3b             	mov    %rdi,(%rbx)
            mailboxes[b].higher = &data[1];
    5519:	48 8d 47 20          	lea    0x20(%rdi),%rax
    551d:	48 89 ca             	mov    %rcx,%rdx
    5520:	48 c1 ea 03          	shr    $0x3,%rdx
    5524:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    552b:	0f 85 58 1f 00 00    	jne    7489 <main+0x29f9>
            mailboxes[b].kind = MAILBOX_FOREIGN;
    5531:	48 8d 73 20          	lea    0x20(%rbx),%rsi
            mailboxes[b].higher = &data[1];
    5535:	48 89 43 08          	mov    %rax,0x8(%rbx)
            mailboxes[b].kind = MAILBOX_FOREIGN;
    5539:	48 89 f2             	mov    %rsi,%rdx
    553c:	48 c1 ea 03          	shr    $0x3,%rdx
    5540:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    5547:	84 d2                	test   %dl,%dl
    5549:	74 09                	je     5554 <main+0xac4>
    554b:	80 fa 03             	cmp    $0x3,%dl
    554e:	0f 8e 3d 1f 00 00    	jle    7491 <main+0x2a01>
            data[0].available = 0;
    5554:	48 8d 77 18          	lea    0x18(%rdi),%rsi
            mailboxes[b].kind = MAILBOX_FOREIGN;
    5558:	c7 43 20 02 00 00 00 	movl   $0x2,0x20(%rbx)
            data[0].available = 0;
    555f:	48 89 f2             	mov    %rsi,%rdx
    5562:	48 c1 ea 03          	shr    $0x3,%rdx
    5566:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    556d:	84 d2                	test   %dl,%dl
    556f:	74 09                	je     557a <main+0xaea>
    5571:	80 fa 03             	cmp    $0x3,%dl
    5574:	0f 8e 1f 1f 00 00    	jle    7499 <main+0x2a09>
            data[0].messages = messages;
    557a:	48 89 fa             	mov    %rdi,%rdx
            data[0].available = 0;
    557d:	c7 47 18 00 00 00 00 	movl   $0x0,0x18(%rdi)
            data[0].messages = messages;
    5584:	48 c1 ea 03          	shr    $0x3,%rdx
    5588:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    558f:	0f 85 0c 1f 00 00    	jne    74a1 <main+0x2a11>
            data[1].messages = messages2;
    5595:	48 89 c2             	mov    %rax,%rdx
            data[0].messages = messages;
    5598:	48 89 2f             	mov    %rbp,(%rdi)
            data[1].messages = messages2;
    559b:	48 c1 ea 03          	shr    $0x3,%rdx
    559f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    55a6:	0f 85 fa 1e 00 00    	jne    74a6 <main+0x2a16>
            data[1].available = 0;
    55ac:	48 8d 4f 38          	lea    0x38(%rdi),%rcx
            data[1].messages = messages2;
    55b0:	4c 89 6f 20          	mov    %r13,0x20(%rdi)
            data[1].available = 0;
    55b4:	48 89 c8             	mov    %rcx,%rax
    55b7:	48 c1 e8 03          	shr    $0x3,%rax
    55bb:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    55c2:	84 c0                	test   %al,%al
    55c4:	74 08                	je     55ce <main+0xb3e>
    55c6:	3c 03                	cmp    $0x3,%al
    55c8:	0f 8e e0 1e 00 00    	jle    74ae <main+0x2a1e>
            data[0].messages_limit = messages_limit;
    55ce:	48 8d 47 10          	lea    0x10(%rdi),%rax
            data[1].available = 0;
    55d2:	c7 47 38 00 00 00 00 	movl   $0x0,0x38(%rdi)
            data[0].messages_limit = messages_limit;
    55d9:	48 89 c2             	mov    %rax,%rdx
    55dc:	48 c1 ea 03          	shr    $0x3,%rdx
    55e0:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    55e7:	0f 85 c9 1e 00 00    	jne    74b6 <main+0x2a26>
            data[0].messages_count = 0;
    55ed:	48 8d 47 08          	lea    0x8(%rdi),%rax
            data[0].messages_limit = messages_limit;
    55f1:	48 c7 47 10 01 00 00 00 	movq   $0x1,0x10(%rdi)
            data[0].messages_count = 0;
    55f9:	48 89 c2             	mov    %rax,%rdx
    55fc:	48 c1 ea 03          	shr    $0x3,%rdx
    5600:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    5607:	0f 85 b1 1e 00 00    	jne    74be <main+0x2a2e>
            data[1].messages_count = 0;
    560d:	48 8d 47 28          	lea    0x28(%rdi),%rax
            data[0].messages_count = 0;
    5611:	48 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%rdi)
            data[1].messages_count = 0;
    5619:	48 89 c2             	mov    %rax,%rdx
    561c:	48 c1 ea 03          	shr    $0x3,%rdx
    5620:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    5627:	0f 85 99 1e 00 00    	jne    74c6 <main+0x2a36>
            data[1].messages_limit = messages_limit;
    562d:	48 8d 47 30          	lea    0x30(%rdi),%rax
            data[1].messages_count = 0;
    5631:	48 c7 47 28 00 00 00 00 	movq   $0x0,0x28(%rdi)
            data[1].messages_limit = messages_limit;
    5639:	48 89 c2             	mov    %rax,%rdx
    563c:	48 c1 ea 03          	shr    $0x3,%rdx
    5640:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    5647:	0f 85 81 1e 00 00    	jne    74ce <main+0x2a3e>
    564d:	48 c7 47 30 01 00 00 00 	movq   $0x1,0x30(%rdi)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    5655:	41 83 c7 01          	add    $0x1,%r15d
    5659:	48 83 c3 28          	add    $0x28,%rbx
    565d:	41 83 ff 0c          	cmp    $0xc,%r15d
    5661:	0f 85 39 fe ff ff    	jne    54a0 <main+0xa10>
          char *message = malloc(sizeof(char) * 256);
    5667:	be 01 00 00 00       	mov    $0x1,%esi
    566c:	bf 00 01 00 00       	mov    $0x100,%edi
    5671:	44 89 e5             	mov    %r12d,%ebp
    5674:	44 8b 64 24 20       	mov    0x20(%rsp),%r12d
    5679:	e8 e2 ed ff ff       	call   4460 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    567e:	bf 18 00 00 00       	mov    $0x18,%edi
          char *message = malloc(sizeof(char) * 256);
    5683:	48 89 c3             	mov    %rax,%rbx
          struct Message *messaged = malloc(sizeof(struct Message));
    5686:	e8 05 ef ff ff       	call   4590 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    568b:	45 89 e1             	mov    %r12d,%r9d
    568e:	41 89 e8             	mov    %ebp,%r8d
    5691:	ba 00 01 00 00       	mov    $0x100,%edx
    5696:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    569b:	48 8d 0d 7e bf 00 00 	lea    0xbf7e(%rip),%rcx        # 11620 <_IO_stdin_used+0x1620>
    56a2:	31 c0                	xor    %eax,%eax
    56a4:	48 89 df             	mov    %rbx,%rdi
    56a7:	be 01 00 00 00       	mov    $0x1,%esi
    56ac:	e8 6f f0 ff ff       	call   4720 <__sprintf_chk@plt>
          messaged->message = message;
    56b1:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    56b6:	4c 89 d8             	mov    %r11,%rax
    56b9:	48 c1 e8 03          	shr    $0x3,%rax
    56bd:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    56c4:	0f 85 66 22 00 00    	jne    7930 <main+0x2ea0>
          messaged->task_index = y;
    56ca:	49 8d 7b 10          	lea    0x10(%r11),%rdi
          messaged->message = message;
    56ce:	49 89 1b             	mov    %rbx,(%r11)
          messaged->task_index = y;
    56d1:	48 89 f8             	mov    %rdi,%rax
    56d4:	48 c1 e8 03          	shr    $0x3,%rax
    56d8:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    56df:	0f 85 9a 1e 00 00    	jne    757f <main+0x2aef>
    56e5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
          messaged->thread_index = thread_data[x].thread_index;
    56ea:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
          messaged->task_index = y;
    56ef:	49 89 43 10          	mov    %rax,0x10(%r11)
          messaged->thread_index = thread_data[x].thread_index;
    56f3:	48 89 d8             	mov    %rbx,%rax
    56f6:	48 c1 e8 03          	shr    $0x3,%rax
    56fa:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    5701:	48 89 d8             	mov    %rbx,%rax
    5704:	83 e0 07             	and    $0x7,%eax
    5707:	83 c0 03             	add    $0x3,%eax
    570a:	38 d0                	cmp    %dl,%al
    570c:	7c 08                	jl     5716 <main+0xc86>
    570e:	84 d2                	test   %dl,%dl
    5710:	0f 85 61 1e 00 00    	jne    7577 <main+0x2ae7>
    5716:	48 8b 04 24          	mov    (%rsp),%rax
    571a:	49 8d 7b 08          	lea    0x8(%r11),%rdi
    571e:	48 89 fa             	mov    %rdi,%rdx
    5721:	48 63 40 04          	movslq 0x4(%rax),%rax
    5725:	48 c1 ea 03          	shr    $0x3,%rdx
    5729:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    5730:	49 89 c7             	mov    %rax,%r15
    5733:	0f 85 39 1e 00 00    	jne    7572 <main+0x2ae2>
    5739:	49 89 43 08          	mov    %rax,0x8(%r11)
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    573d:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5742:	48 c1 e8 03          	shr    $0x3,%rax
    5746:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    574d:	0f 85 15 1e 00 00    	jne    7568 <main+0x2ad8>
    5753:	48 8b 04 24          	mov    (%rsp),%rax
    5757:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
    575c:	48 8b 50 38          	mov    0x38(%rax),%rdx
    5760:	48 01 d3             	add    %rdx,%rbx
    5763:	48 89 d8             	mov    %rbx,%rax
    5766:	48 c1 e8 03          	shr    $0x3,%rax
    576a:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    5771:	84 c0                	test   %al,%al
    5773:	74 08                	je     577d <main+0xced>
    5775:	3c 03                	cmp    $0x3,%al
    5777:	0f 8e e3 1d 00 00    	jle    7560 <main+0x2ad0>
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    577d:	48 8d bb 90 01 00 00 	lea    0x190(%rbx),%rdi
    5784:	41 8d 44 24 01       	lea    0x1(%r12),%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    5789:	c7 03 41 00 00 00    	movl   $0x41,(%rbx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    578f:	48 89 f9             	mov    %rdi,%rcx
    5792:	83 e0 01             	and    $0x1,%eax
    5795:	48 c1 e9 03          	shr    $0x3,%rcx
    5799:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    57a0:	84 c9                	test   %cl,%cl
    57a2:	74 09                	je     57ad <main+0xd1d>
    57a4:	80 f9 03             	cmp    $0x3,%cl
    57a7:	0f 8e ae 1d 00 00    	jle    755b <main+0x2acb>
          thread_data[x].tasks[y].message = messaged;
    57ad:	48 8d bb 88 01 00 00 	lea    0x188(%rbx),%rdi
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    57b4:	89 83 90 01 00 00    	mov    %eax,0x190(%rbx)
          thread_data[x].tasks[y].message = messaged;
    57ba:	48 89 f8             	mov    %rdi,%rax
    57bd:	48 c1 e8 03          	shr    $0x3,%rax
    57c1:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    57c8:	0f 85 88 1d 00 00    	jne    7556 <main+0x2ac6>
          thread_data[x].tasks[y].sending = 1;
    57ce:	48 8d bb 80 01 00 00 	lea    0x180(%rbx),%rdi
          thread_data[x].tasks[y].message = messaged;
    57d5:	4c 89 9b 88 01 00 00 	mov    %r11,0x188(%rbx)
          thread_data[x].tasks[y].sending = 1;
    57dc:	48 89 f8             	mov    %rdi,%rax
    57df:	48 c1 e8 03          	shr    $0x3,%rax
    57e3:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    57ea:	84 c0                	test   %al,%al
    57ec:	74 08                	je     57f6 <main+0xd66>
    57ee:	3c 03                	cmp    $0x3,%al
    57f0:	0f 8e 5b 1d 00 00    	jle    7551 <main+0x2ac1>
          thread_data[x].tasks[y].snapshot_count = 99;
    57f6:	48 8d bb 58 01 00 00 	lea    0x158(%rbx),%rdi
          thread_data[x].tasks[y].sending = 1;
    57fd:	c7 83 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rbx)
          thread_data[x].tasks[y].snapshot_count = 99;
    5807:	48 89 f8             	mov    %rdi,%rax
    580a:	48 c1 e8 03          	shr    $0x3,%rax
    580e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5815:	0f 85 c3 1d 00 00    	jne    75de <main+0x2b4e>
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    581b:	bf 63 00 00 00       	mov    $0x63,%edi
    5820:	be 20 00 00 00       	mov    $0x20,%esi
    5825:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
          thread_data[x].tasks[y].snapshot_count = 99;
    582a:	48 c7 83 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    5835:	e8 26 ec ff ff       	call   4460 <calloc@plt>
    583a:	48 8d bb 50 01 00 00 	lea    0x150(%rbx),%rdi
    5841:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    5846:	48 89 f9             	mov    %rdi,%rcx
    5849:	48 c1 e9 03          	shr    $0x3,%rcx
    584d:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    5854:	0f 85 7f 1d 00 00    	jne    75d9 <main+0x2b49>
          thread_data[x].tasks[y].current_snapshot = 0;
    585a:	48 8d bb 60 01 00 00 	lea    0x160(%rbx),%rdi
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    5861:	48 89 83 50 01 00 00 	mov    %rax,0x150(%rbx)
          thread_data[x].tasks[y].current_snapshot = 0;
    5868:	48 89 f8             	mov    %rdi,%rax
    586b:	48 c1 e8 03          	shr    $0x3,%rax
    586f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5876:	0f 85 58 1d 00 00    	jne    75d4 <main+0x2b44>
    587c:	48 c7 83 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    5887:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    588c:	48 c1 e8 03          	shr    $0x3,%rax
    5890:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5897:	0f 85 2d 1d 00 00    	jne    75ca <main+0x2b3a>
    589d:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    58a2:	48 8b 00             	mov    (%rax),%rax
    58a5:	48 8d 78 04          	lea    0x4(%rax),%rdi
    58a9:	48 89 f9             	mov    %rdi,%rcx
    58ac:	48 c1 e9 03          	shr    $0x3,%rcx
    58b0:	0f b6 b1 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%esi
    58b7:	48 89 f9             	mov    %rdi,%rcx
    58ba:	83 e1 07             	and    $0x7,%ecx
    58bd:	83 c1 03             	add    $0x3,%ecx
    58c0:	40 38 f1             	cmp    %sil,%cl
    58c3:	7c 09                	jl     58ce <main+0xe3e>
    58c5:	40 84 f6             	test   %sil,%sil
    58c8:	0f 85 f7 1c 00 00    	jne    75c5 <main+0x2b35>
    58ce:	48 8d bb 30 01 00 00 	lea    0x130(%rbx),%rdi
    58d5:	8b 70 04             	mov    0x4(%rax),%esi
    58d8:	48 89 f9             	mov    %rdi,%rcx
    58db:	48 c1 e9 03          	shr    $0x3,%rcx
    58df:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    58e6:	84 c9                	test   %cl,%cl
    58e8:	74 09                	je     58f3 <main+0xe63>
    58ea:	80 f9 03             	cmp    $0x3,%cl
    58ed:	0f 8e cd 1c 00 00    	jle    75c0 <main+0x2b30>
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    58f3:	48 8d bb 28 01 00 00 	lea    0x128(%rbx),%rdi
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    58fa:	89 b3 30 01 00 00    	mov    %esi,0x130(%rbx)
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    5900:	48 89 f9             	mov    %rdi,%rcx
    5903:	48 c1 e9 03          	shr    $0x3,%rcx
    5907:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    590e:	0f 85 a7 1c 00 00    	jne    75bb <main+0x2b2b>
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    5914:	48 8b 34 24          	mov    (%rsp),%rsi
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    5918:	48 89 83 28 01 00 00 	mov    %rax,0x128(%rbx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    591f:	48 39 f0             	cmp    %rsi,%rax
    5922:	0f 85 84 1c 00 00    	jne    75ac <main+0x2b1c>
          thread_data[x].tasks[y].available = 1;
    5928:	48 8d bb 44 01 00 00 	lea    0x144(%rbx),%rdi
    592f:	48 89 f8             	mov    %rdi,%rax
    5932:	48 c1 e8 03          	shr    $0x3,%rax
    5936:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    593d:	48 89 f8             	mov    %rdi,%rax
    5940:	83 e0 07             	and    $0x7,%eax
    5943:	83 c0 03             	add    $0x3,%eax
    5946:	38 c8                	cmp    %cl,%al
    5948:	7c 08                	jl     5952 <main+0xec2>
    594a:	84 c9                	test   %cl,%cl
    594c:	0f 85 55 1c 00 00    	jne    75a7 <main+0x2b17>
          thread_data[x].tasks[y].arrived = 0;
    5952:	48 8d bb 80 00 00 00 	lea    0x80(%rbx),%rdi
          thread_data[x].tasks[y].available = 1;
    5959:	c7 83 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rbx)
          thread_data[x].tasks[y].arrived = 0;
    5963:	48 89 f8             	mov    %rdi,%rax
    5966:	48 c1 e8 03          	shr    $0x3,%rax
    596a:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    5971:	84 c0                	test   %al,%al
    5973:	74 08                	je     597d <main+0xeed>
    5975:	3c 03                	cmp    $0x3,%al
    5977:	0f 8e 25 1c 00 00    	jle    75a2 <main+0x2b12>
          thread_data[x].tasks[y].thread_count = 2;
    597d:	48 8d bb 34 01 00 00 	lea    0x134(%rbx),%rdi
          thread_data[x].tasks[y].arrived = 0;
    5984:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
          thread_data[x].tasks[y].thread_count = 2;
    598e:	48 89 f8             	mov    %rdi,%rax
    5991:	48 c1 e8 03          	shr    $0x3,%rax
    5995:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    599c:	48 89 f8             	mov    %rdi,%rax
    599f:	83 e0 07             	and    $0x7,%eax
    59a2:	83 c0 03             	add    $0x3,%eax
    59a5:	38 c8                	cmp    %cl,%al
    59a7:	7c 08                	jl     59b1 <main+0xf21>
    59a9:	84 c9                	test   %cl,%cl
    59ab:	0f 85 ec 1b 00 00    	jne    759d <main+0x2b0d>
          thread_data[x].tasks[y].total_thread_count = thread_count;
    59b1:	48 8d bb 38 01 00 00 	lea    0x138(%rbx),%rdi
          thread_data[x].tasks[y].thread_count = 2;
    59b8:	c7 83 34 01 00 00 02 00 00 00 	movl   $0x2,0x134(%rbx)
          thread_data[x].tasks[y].total_thread_count = thread_count;
    59c2:	48 89 f8             	mov    %rdi,%rax
    59c5:	48 c1 e8 03          	shr    $0x3,%rax
    59c9:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    59d0:	84 c0                	test   %al,%al
    59d2:	74 08                	je     59dc <main+0xf4c>
    59d4:	3c 03                	cmp    $0x3,%al
    59d6:	0f 8e bc 1b 00 00    	jle    7598 <main+0x2b08>
          thread_data[x].tasks[y].all_thread_count = thread_count;
    59dc:	48 8d bb 3c 01 00 00 	lea    0x13c(%rbx),%rdi
          thread_data[x].tasks[y].total_thread_count = thread_count;
    59e3:	c7 83 38 01 00 00 02 00 00 00 	movl   $0x2,0x138(%rbx)
          thread_data[x].tasks[y].all_thread_count = thread_count;
    59ed:	48 89 f8             	mov    %rdi,%rax
    59f0:	48 c1 e8 03          	shr    $0x3,%rax
    59f4:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    59fb:	48 89 f8             	mov    %rdi,%rax
    59fe:	83 e0 07             	and    $0x7,%eax
    5a01:	83 c0 03             	add    $0x3,%eax
    5a04:	38 c8                	cmp    %cl,%al
    5a06:	7c 08                	jl     5a10 <main+0xf80>
    5a08:	84 c9                	test   %cl,%cl
    5a0a:	0f 85 83 1b 00 00    	jne    7593 <main+0x2b03>
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
    5a10:	48 8d bb 40 01 00 00 	lea    0x140(%rbx),%rdi
          thread_data[x].tasks[y].all_thread_count = thread_count;
    5a17:	c7 83 3c 01 00 00 02 00 00 00 	movl   $0x2,0x13c(%rbx)
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
    5a21:	48 89 f8             	mov    %rdi,%rax
    5a24:	48 c1 e8 03          	shr    $0x3,%rax
    5a28:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    5a2f:	84 c0                	test   %al,%al
    5a31:	74 08                	je     5a3b <main+0xfab>
    5a33:	3c 03                	cmp    $0x3,%al
    5a35:	0f 8e 53 1b 00 00    	jle    758e <main+0x2afe>
          thread_data[x].tasks[y].task_count = total_barrier_count;
    5a3b:	48 8d bb 48 01 00 00 	lea    0x148(%rbx),%rdi
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
    5a42:	c7 83 40 01 00 00 0c 00 00 00 	movl   $0xc,0x140(%rbx)
          thread_data[x].tasks[y].task_count = total_barrier_count;
    5a4c:	48 89 f8             	mov    %rdi,%rax
    5a4f:	48 c1 e8 03          	shr    $0x3,%rax
    5a53:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    5a5a:	84 c0                	test   %al,%al
    5a5c:	74 08                	je     5a66 <main+0xfd6>
    5a5e:	3c 03                	cmp    $0x3,%al
    5a60:	0f 8e 23 1b 00 00    	jle    7589 <main+0x2af9>
          thread_data[x].tasks[y].worker_count = thread_count;
    5a66:	48 8d bb 84 01 00 00 	lea    0x184(%rbx),%rdi
          thread_data[x].tasks[y].task_count = total_barrier_count;
    5a6d:	c7 83 48 01 00 00 03 00 00 00 	movl   $0x3,0x148(%rbx)
          thread_data[x].tasks[y].worker_count = thread_count;
    5a77:	48 89 f8             	mov    %rdi,%rax
    5a7a:	48 c1 e8 03          	shr    $0x3,%rax
    5a7e:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    5a85:	48 89 f8             	mov    %rdi,%rax
    5a88:	83 e0 07             	and    $0x7,%eax
    5a8b:	83 c0 03             	add    $0x3,%eax
    5a8e:	38 c8                	cmp    %cl,%al
    5a90:	7c 08                	jl     5a9a <main+0x100a>
    5a92:	84 c9                	test   %cl,%cl
    5a94:	0f 85 ea 1a 00 00    	jne    7584 <main+0x2af4>
    5a9a:	c7 83 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rbx)
          thread_data[x].tasks[y].task_index = y;
    5aa4:	48 8d 7b 04          	lea    0x4(%rbx),%rdi
    5aa8:	48 89 f8             	mov    %rdi,%rax
    5aab:	48 c1 e8 03          	shr    $0x3,%rax
    5aaf:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    5ab6:	48 89 f8             	mov    %rdi,%rax
    5ab9:	83 e0 07             	and    $0x7,%eax
    5abc:	83 c0 03             	add    $0x3,%eax
    5abf:	38 c8                	cmp    %cl,%al
    5ac1:	7c 08                	jl     5acb <main+0x103b>
    5ac3:	84 c9                	test   %cl,%cl
    5ac5:	0f 85 45 1a 00 00    	jne    7510 <main+0x2a80>
    5acb:	44 89 63 04          	mov    %r12d,0x4(%rbx)
          if (y == barrier_count - 1) {
    5acf:	41 83 fc 01          	cmp    $0x1,%r12d
    5ad3:	0f 84 eb 02 00 00    	je     5dc4 <main+0x1334>
            if (y == 0) {
    5ad9:	45 85 e4             	test   %r12d,%r12d
    5adc:	0f 84 ae 02 00 00    	je     5d90 <main+0x1300>
               thread_data[x].tasks[y].run = barriered_work; 
    5ae2:	48 8d bb 18 01 00 00 	lea    0x118(%rbx),%rdi
    5ae9:	45 89 fd             	mov    %r15d,%r13d
    5aec:	4c 8b 14 24          	mov    (%rsp),%r10
    5af0:	49 89 d7             	mov    %rdx,%r15
    5af3:	48 89 f8             	mov    %rdi,%rax
    5af6:	48 c1 e8 03          	shr    $0x3,%rax
    5afa:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5b01:	0f 85 04 1a 00 00    	jne    750b <main+0x2a7b>
    5b07:	48 8d 05 32 8d 00 00 	lea    0x8d32(%rip),%rax        # e840 <barriered_work>
        thread_data[x].buffers_count = buffers_per_thread;
    5b0e:	49 8d ba bc 00 00 00 	lea    0xbc(%r10),%rdi
               thread_data[x].tasks[y].run = barriered_work; 
    5b15:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        thread_data[x].buffers_count = buffers_per_thread;
    5b1c:	48 89 f8             	mov    %rdi,%rax
    5b1f:	48 c1 e8 03          	shr    $0x3,%rax
    5b23:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    5b2a:	48 89 f8             	mov    %rdi,%rax
    5b2d:	83 e0 07             	and    $0x7,%eax
    5b30:	83 c0 03             	add    $0x3,%eax
    5b33:	38 d0                	cmp    %dl,%al
    5b35:	7c 08                	jl     5b3f <main+0x10af>
    5b37:	84 d2                	test   %dl,%dl
    5b39:	0f 85 c7 19 00 00    	jne    7506 <main+0x2a76>
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    5b3f:	bf 01 00 00 00       	mov    $0x1,%edi
    5b44:	be 08 00 00 00       	mov    $0x8,%esi
        thread_data[x].buffers_count = buffers_per_thread;
    5b49:	4c 89 14 24          	mov    %r10,(%rsp)
    5b4d:	41 c7 82 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r10)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    5b58:	e8 03 e9 ff ff       	call   4460 <calloc@plt>
    5b5d:	4c 8b 14 24          	mov    (%rsp),%r10
    5b61:	48 89 c7             	mov    %rax,%rdi
    5b64:	49 8d 42 50          	lea    0x50(%r10),%rax
    5b68:	48 89 c2             	mov    %rax,%rdx
    5b6b:	48 c1 ea 03          	shr    $0x3,%rdx
    5b6f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    5b76:	0f 85 82 19 00 00    	jne    74fe <main+0x2a6e>
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    5b7c:	48 89 f8             	mov    %rdi,%rax
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    5b7f:	49 89 7a 50          	mov    %rdi,0x50(%r10)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    5b83:	48 c1 e8 03          	shr    $0x3,%rax
    5b87:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5b8e:	0f 85 65 19 00 00    	jne    74f9 <main+0x2a69>
    5b94:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    5b99:	48 89 07             	mov    %rax,(%rdi)
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
    5b9c:	49 8d bf 20 05 00 00 	lea    0x520(%r15),%rdi
    5ba3:	48 89 f8             	mov    %rdi,%rax
    5ba6:	48 c1 e8 03          	shr    $0x3,%rax
    5baa:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5bb1:	0f 85 3d 19 00 00    	jne    74f4 <main+0x2a64>
    5bb7:	48 8d 05 b2 1e 00 00 	lea    0x1eb2(%rip),%rax        # 7a70 <do_protected_write>
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    5bbe:	49 8d bf 18 05 00 00 	lea    0x518(%r15),%rdi
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
    5bc5:	49 89 87 20 05 00 00 	mov    %rax,0x520(%r15)
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    5bcc:	48 89 f8             	mov    %rdi,%rax
    5bcf:	48 c1 e8 03          	shr    $0x3,%rax
    5bd3:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5bda:	0f 85 0f 19 00 00    	jne    74ef <main+0x2a5f>
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    5be0:	49 8d bf 28 05 00 00 	lea    0x528(%r15),%rdi
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    5be7:	48 8d 05 62 1f 00 00 	lea    0x1f62(%rip),%rax        # 7b50 <barriered_reset>
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    5bee:	48 89 fa             	mov    %rdi,%rdx
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    5bf1:	49 89 87 18 05 00 00 	mov    %rax,0x518(%r15)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    5bf8:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5bfd:	48 c1 ea 03          	shr    $0x3,%rdx
    5c01:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    5c08:	48 8b 00             	mov    (%rax),%rax
    5c0b:	0f 85 d9 18 00 00    	jne    74ea <main+0x2a5a>
        thread_data[x].tasks[barrier_count].available = 1; 
    5c11:	49 8d bf 44 05 00 00 	lea    0x544(%r15),%rdi
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    5c18:	49 89 87 28 05 00 00 	mov    %rax,0x528(%r15)
        thread_data[x].tasks[barrier_count].available = 1; 
    5c1f:	48 89 f8             	mov    %rdi,%rax
    5c22:	48 c1 e8 03          	shr    $0x3,%rax
    5c26:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    5c2d:	48 89 f8             	mov    %rdi,%rax
    5c30:	83 e0 07             	and    $0x7,%eax
    5c33:	83 c0 03             	add    $0x3,%eax
    5c36:	38 d0                	cmp    %dl,%al
    5c38:	7c 08                	jl     5c42 <main+0x11b2>
    5c3a:	84 d2                	test   %dl,%dl
    5c3c:	0f 85 a3 18 00 00    	jne    74e5 <main+0x2a55>
        thread_data[x].tasks[barrier_count].arrived = 0; 
    5c42:	49 8d bf 80 04 00 00 	lea    0x480(%r15),%rdi
        thread_data[x].tasks[barrier_count].available = 1; 
    5c49:	41 c7 87 44 05 00 00 01 00 00 00 	movl   $0x1,0x544(%r15)
        thread_data[x].tasks[barrier_count].arrived = 0; 
    5c54:	48 89 f8             	mov    %rdi,%rax
    5c57:	48 c1 e8 03          	shr    $0x3,%rax
    5c5b:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    5c62:	84 c0                	test   %al,%al
    5c64:	74 08                	je     5c6e <main+0x11de>
    5c66:	3c 03                	cmp    $0x3,%al
    5c68:	0f 8e 0a 1b 00 00    	jle    7778 <main+0x2ce8>
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    5c6e:	49 8d bf 04 04 00 00 	lea    0x404(%r15),%rdi
        thread_data[x].tasks[barrier_count].arrived = 0; 
    5c75:	41 c7 87 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r15)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    5c80:	48 89 f8             	mov    %rdi,%rax
    5c83:	48 c1 e8 03          	shr    $0x3,%rax
    5c87:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    5c8e:	48 89 f8             	mov    %rdi,%rax
    5c91:	83 e0 07             	and    $0x7,%eax
    5c94:	83 c0 03             	add    $0x3,%eax
    5c97:	38 d0                	cmp    %dl,%al
    5c99:	7c 08                	jl     5ca3 <main+0x1213>
    5c9b:	84 d2                	test   %dl,%dl
    5c9d:	0f 85 d0 1a 00 00    	jne    7773 <main+0x2ce3>
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    5ca3:	49 8d bf 34 05 00 00 	lea    0x534(%r15),%rdi
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    5caa:	41 c7 87 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%r15)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    5cb5:	48 89 f8             	mov    %rdi,%rax
    5cb8:	48 c1 e8 03          	shr    $0x3,%rax
    5cbc:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    5cc3:	48 89 f8             	mov    %rdi,%rax
    5cc6:	83 e0 07             	and    $0x7,%eax
    5cc9:	83 c0 03             	add    $0x3,%eax
    5ccc:	38 d0                	cmp    %dl,%al
    5cce:	7c 08                	jl     5cd8 <main+0x1248>
    5cd0:	84 d2                	test   %dl,%dl
    5cd2:	0f 85 96 1a 00 00    	jne    776e <main+0x2cde>
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    5cd8:	49 8d bf 30 05 00 00 	lea    0x530(%r15),%rdi
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    5cdf:	41 c7 87 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r15)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    5cea:	48 89 f8             	mov    %rdi,%rax
    5ced:	48 c1 e8 03          	shr    $0x3,%rax
    5cf1:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    5cf8:	84 c0                	test   %al,%al
    5cfa:	74 08                	je     5d04 <main+0x1274>
    5cfc:	3c 03                	cmp    $0x3,%al
    5cfe:	0f 8e 65 1a 00 00    	jle    7769 <main+0x2cd9>
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    5d04:	49 8d bf 84 05 00 00 	lea    0x584(%r15),%rdi
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    5d0b:	45 89 af 30 05 00 00 	mov    %r13d,0x530(%r15)
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    5d12:	48 89 f8             	mov    %rdi,%rax
    5d15:	48 c1 e8 03          	shr    $0x3,%rax
    5d19:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    5d20:	48 89 f8             	mov    %rdi,%rax
    5d23:	83 e0 07             	and    $0x7,%eax
    5d26:	83 c0 03             	add    $0x3,%eax
    5d29:	38 d0                	cmp    %dl,%al
    5d2b:	7c 08                	jl     5d35 <main+0x12a5>
    5d2d:	84 d2                	test   %dl,%dl
    5d2f:	0f 85 2f 1a 00 00    	jne    7764 <main+0x2cd4>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    5d35:	49 8d bf 48 05 00 00 	lea    0x548(%r15),%rdi
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    5d3c:	41 c7 87 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%r15)
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    5d47:	48 89 f8             	mov    %rdi,%rax
    5d4a:	48 c1 e8 03          	shr    $0x3,%rax
    5d4e:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    5d55:	84 c0                	test   %al,%al
    5d57:	74 08                	je     5d61 <main+0x12d1>
    5d59:	3c 03                	cmp    $0x3,%al
    5d5b:	0f 8e fe 19 00 00    	jle    775f <main+0x2ccf>
    for (int d = 0 ; d < threads_per_group ; d++) {
    5d61:	8b 5c 24 58          	mov    0x58(%rsp),%ebx
    5d65:	41 8d 46 01          	lea    0x1(%r14),%eax
    5d69:	48 83 44 24 40 10    	addq   $0x10,0x40(%rsp)
    5d6f:	83 c5 01             	add    $0x1,%ebp
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    5d72:	41 c7 87 48 05 00 00 03 00 00 00 	movl   $0x3,0x548(%r15)
    for (int d = 0 ; d < threads_per_group ; d++) {
    5d7d:	49 81 c2 c0 00 00 00 	add    $0xc0,%r10
    5d84:	39 d8                	cmp    %ebx,%eax
    5d86:	74 4b                	je     5dd3 <main+0x1343>
    5d88:	41 89 c6             	mov    %eax,%r14d
    5d8b:	e9 a2 f0 ff ff       	jmp    4e32 <main+0x3a2>
    5d90:	48 8d 0d 39 93 00 00 	lea    0x9339(%rip),%rcx        # f0d0 <barriered_work_ingest_andwork>
    5d97:	41 bc 01 00 00 00    	mov    $0x1,%r12d
            thread_data[x].tasks[y].run = barriered_work; 
    5d9d:	48 8d bb 18 01 00 00 	lea    0x118(%rbx),%rdi
    5da4:	48 89 f8             	mov    %rdi,%rax
    5da7:	48 c1 e8 03          	shr    $0x3,%rax
    5dab:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5db2:	0f 85 a2 19 00 00    	jne    775a <main+0x2cca>
    5db8:	48 89 8b 18 01 00 00 	mov    %rcx,0x118(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    5dbf:	e9 b7 f4 ff ff       	jmp    527b <main+0x7eb>
    5dc4:	48 8d 0d 75 8a 00 00 	lea    0x8a75(%rip),%rcx        # e840 <barriered_work>
    5dcb:	41 bc 02 00 00 00    	mov    $0x2,%r12d
    5dd1:	eb ca                	jmp    5d9d <main+0x130d>
    5dd3:	4c 8b 4c 24 70       	mov    0x70(%rsp),%r9
  for (int k = 0 ; k < group_count ; k++) {
    5dd8:	48 83 44 24 60 18    	addq   $0x18,0x60(%rsp)
    5dde:	49 83 c1 01          	add    $0x1,%r9
    5de2:	49 83 f9 06          	cmp    $0x6,%r9
    5de6:	74 52                	je     5e3a <main+0x13aa>
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    5de8:	8b 54 24 7c          	mov    0x7c(%rsp),%edx
    5dec:	44 01 f2             	add    %r14d,%edx
    5def:	e9 f7 ef ff ff       	jmp    4deb <main+0x35b>
        my_thread_data[1] = &thread_data[other]; 
    5df4:	49 63 c6             	movslq %r14d,%rax
    5df7:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
        other = (x + 1) % total_threads;
    5dfc:	44 89 f3             	mov    %r14d,%ebx
        my_thread_data[1] = &thread_data[other]; 
    5dff:	45 31 c0             	xor    %r8d,%r8d
    5e02:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
    5e06:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    5e0b:	48 c1 e2 06          	shl    $0x6,%rdx
    5e0f:	48 01 c2             	add    %rax,%rdx
        my_thread_data[0] = &thread_data[x]; 
    5e12:	4c 89 d0             	mov    %r10,%rax
    5e15:	e9 90 f0 ff ff       	jmp    4eaa <main+0x41a>
            CPU_SET(j, sendercpu);
    5e1a:	4c 89 f8             	mov    %r15,%rax
    5e1d:	48 c1 e8 03          	shr    $0x3,%rax
    5e21:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5e28:	0f 85 1b 17 00 00    	jne    7549 <main+0x2ab9>
    5e2e:	49 81 0f ff 0f 00 00 	orq    $0xfff,(%r15)
          for (int j = 0 ; j < cores ; j++) {
    5e35:	e9 a8 f1 ff ff       	jmp    4fe2 <main+0x552>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5e3a:	4c 8b 5c 24 48       	mov    0x48(%rsp),%r11
    5e3f:	ba 0d 00 00 00       	mov    $0xd,%edx
    5e44:	48 8d 35 35 b8 00 00 	lea    0xb835(%rip),%rsi        # 11680 <_IO_stdin_used+0x1680>
    5e4b:	31 c0                	xor    %eax,%eax
    5e4d:	bf 01 00 00 00       	mov    $0x1,%edi
    5e52:	4c 89 1c 24          	mov    %r11,(%rsp)
    5e56:	e8 c5 e6 ff ff       	call   4520 <__printf_chk@plt>
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    5e5b:	bf 02 00 00 00       	mov    $0x2,%edi
    5e60:	be 08 00 00 00       	mov    $0x8,%esi
    5e65:	e8 f6 e5 ff ff       	call   4460 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    5e6a:	4c 8b 1c 24          	mov    (%rsp),%r11
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    5e6e:	48 89 c7             	mov    %rax,%rdi
    my_thread_data[0] = &thread_data[x]; 
    5e71:	49 8d 83 c0 09 00 00 	lea    0x9c0(%r11),%rax
    5e78:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    5e7d:	48 89 f8             	mov    %rdi,%rax
    5e80:	48 c1 e8 03          	shr    $0x3,%rax
    5e84:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5e8b:	0f 85 b3 16 00 00    	jne    7544 <main+0x2ab4>
    5e91:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5e96:	48 89 07             	mov    %rax,(%rdi)
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    5e99:	48 8d 47 08          	lea    0x8(%rdi),%rax
    5e9d:	48 89 c2             	mov    %rax,%rdx
    5ea0:	48 c1 ea 03          	shr    $0x3,%rdx
    5ea4:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    5eab:	0f 85 8b 16 00 00    	jne    753c <main+0x2aac>
    thread_data[x].threads = my_thread_data;
    5eb1:	49 8d 83 d8 09 00 00 	lea    0x9d8(%r11),%rax
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    5eb8:	4c 89 5f 08          	mov    %r11,0x8(%rdi)
    thread_data[x].threads = my_thread_data;
    5ebc:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    5ec1:	48 c1 e8 03          	shr    $0x3,%rax
    5ec5:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5ecc:	0f 85 60 16 00 00    	jne    7532 <main+0x2aa2>
    thread_data[x].thread_count = 2;
    5ed2:	49 8d 83 e8 09 00 00 	lea    0x9e8(%r11),%rax
    thread_data[x].threads = my_thread_data;
    5ed9:	49 89 bb d8 09 00 00 	mov    %rdi,0x9d8(%r11)
    thread_data[x].thread_count = 2;
    5ee0:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    5ee5:	48 c1 e8 03          	shr    $0x3,%rax
    5ee9:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    5ef0:	84 c0                	test   %al,%al
    5ef2:	74 08                	je     5efc <main+0x146c>
    5ef4:	3c 03                	cmp    $0x3,%al
    5ef6:	0f 8e df 15 00 00    	jle    74db <main+0x2a4b>
    thread_data[x].thread_index = 0;
    5efc:	4d 8d bb c4 09 00 00 	lea    0x9c4(%r11),%r15
    thread_data[x].thread_count = 2;
    5f03:	41 c7 83 e8 09 00 00 02 00 00 00 	movl   $0x2,0x9e8(%r11)
    thread_data[x].thread_index = 0;
    5f0e:	4c 89 f8             	mov    %r15,%rax
    5f11:	48 c1 e8 03          	shr    $0x3,%rax
    5f15:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    5f1c:	4c 89 f8             	mov    %r15,%rax
    5f1f:	83 e0 07             	and    $0x7,%eax
    5f22:	83 c0 03             	add    $0x3,%eax
    5f25:	38 d0                	cmp    %dl,%al
    5f27:	7c 08                	jl     5f31 <main+0x14a1>
    5f29:	84 d2                	test   %dl,%dl
    5f2b:	0f 85 0c 1a 00 00    	jne    793d <main+0x2ead>
    thread_data[x].task_count = total_barrier_count;
    5f31:	49 8d 83 00 0a 00 00 	lea    0xa00(%r11),%rax
    thread_data[x].thread_index = 0;
    5f38:	41 c7 83 c4 09 00 00 00 00 00 00 	movl   $0x0,0x9c4(%r11)
    thread_data[x].task_count = total_barrier_count;
    5f43:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    5f48:	48 c1 e8 03          	shr    $0x3,%rax
    5f4c:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    5f53:	84 c0                	test   %al,%al
    5f55:	74 08                	je     5f5f <main+0x14cf>
    5f57:	3c 03                	cmp    $0x3,%al
    5f59:	0f 8e 6c 18 00 00    	jle    77cb <main+0x2d3b>
    5f5f:	41 c7 83 00 0a 00 00 03 00 00 00 	movl   $0x3,0xa00(%r11)
    thread_data[n].tasks[0].scheduled = 1;
    5f6a:	49 8d 43 38          	lea    0x38(%r11),%rax
    5f6e:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    5f73:	48 c1 e8 03          	shr    $0x3,%rax
    5f77:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5f7e:	0f 85 fe 18 00 00    	jne    7882 <main+0x2df2>
    5f84:	49 8b 53 38          	mov    0x38(%r11),%rdx
    5f88:	48 8d ba 4c 01 00 00 	lea    0x14c(%rdx),%rdi
    5f8f:	48 89 f8             	mov    %rdi,%rax
    5f92:	48 c1 e8 03          	shr    $0x3,%rax
    5f96:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    5f9d:	48 89 f8             	mov    %rdi,%rax
    5fa0:	83 e0 07             	and    $0x7,%eax
    5fa3:	83 c0 03             	add    $0x3,%eax
    5fa6:	38 c8                	cmp    %cl,%al
    5fa8:	7c 08                	jl     5fb2 <main+0x1522>
    5faa:	84 c9                	test   %cl,%cl
    5fac:	0f 85 14 18 00 00    	jne    77c6 <main+0x2d36>
    5fb2:	49 8d 83 c0 00 00 00 	lea    0xc0(%r11),%rax
    5fb9:	49 8d bb f8 00 00 00 	lea    0xf8(%r11),%rdi
    5fc0:	c7 82 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rdx)
    5fca:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    5fcf:	48 89 f8             	mov    %rdi,%rax
    5fd2:	48 c1 e8 03          	shr    $0x3,%rax
    5fd6:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5fdd:	0f 85 08 16 00 00    	jne    75eb <main+0x2b5b>
    5fe3:	49 8b 93 f8 00 00 00 	mov    0xf8(%r11),%rdx
    5fea:	48 8d ba 4c 01 00 00 	lea    0x14c(%rdx),%rdi
    5ff1:	48 89 f8             	mov    %rdi,%rax
    5ff4:	48 c1 e8 03          	shr    $0x3,%rax
    5ff8:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    5fff:	48 89 f8             	mov    %rdi,%rax
    6002:	83 e0 07             	and    $0x7,%eax
    6005:	83 c0 03             	add    $0x3,%eax
    6008:	38 c8                	cmp    %cl,%al
    600a:	7c 08                	jl     6014 <main+0x1584>
    600c:	84 c9                	test   %cl,%cl
    600e:	0f 85 ad 17 00 00    	jne    77c1 <main+0x2d31>
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    6014:	be 38 00 00 00       	mov    $0x38,%esi
    6019:	bf 10 00 00 00       	mov    $0x10,%edi
    601e:	4c 89 1c 24          	mov    %r11,(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    6022:	c7 82 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rdx)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    602c:	e8 2f e4 ff ff       	call   4460 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    6031:	be 38 00 00 00       	mov    $0x38,%esi
    6036:	bf 10 00 00 00       	mov    $0x10,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    603b:	49 89 c6             	mov    %rax,%r14
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    603e:	e8 1d e4 ff ff       	call   4460 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    6043:	be 38 00 00 00       	mov    $0x38,%esi
    6048:	bf 10 00 00 00       	mov    $0x10,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    604d:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    6050:	e8 0b e4 ff ff       	call   4460 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    6055:	be 38 00 00 00       	mov    $0x38,%esi
    605a:	bf 10 00 00 00       	mov    $0x10,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    605f:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    6064:	e8 f7 e3 ff ff       	call   4460 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    6069:	bf 10 00 00 00       	mov    $0x10,%edi
    606e:	be 08 00 00 00       	mov    $0x8,%esi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    6073:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    6078:	e8 e3 e3 ff ff       	call   4460 <calloc@plt>
  thread_data[timer_threadi].type = TIMER;
    607d:	4c 8b 1c 24          	mov    (%rsp),%r11
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    6081:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].type = TIMER;
    6084:	49 8d bb 0c 09 00 00 	lea    0x90c(%r11),%rdi
    608b:	48 89 f8             	mov    %rdi,%rax
    608e:	48 c1 e8 03          	shr    $0x3,%rax
    6092:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    6099:	48 89 f8             	mov    %rdi,%rax
    609c:	83 e0 07             	and    $0x7,%eax
    609f:	83 c0 03             	add    $0x3,%eax
    60a2:	38 d0                	cmp    %dl,%al
    60a4:	7c 08                	jl     60ae <main+0x161e>
    60a6:	84 d2                	test   %dl,%dl
    60a8:	0f 85 0e 17 00 00    	jne    77bc <main+0x2d2c>
  thread_data[timer_threadi].running = 1;
    60ae:	49 8d bb 44 09 00 00 	lea    0x944(%r11),%rdi
  thread_data[timer_threadi].type = TIMER;
    60b5:	41 c7 83 0c 09 00 00 00 00 00 00 	movl   $0x0,0x90c(%r11)
  thread_data[timer_threadi].running = 1;
    60c0:	48 89 f8             	mov    %rdi,%rax
    60c3:	48 c1 e8 03          	shr    $0x3,%rax
    60c7:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    60ce:	48 89 f8             	mov    %rdi,%rax
    60d1:	83 e0 07             	and    $0x7,%eax
    60d4:	83 c0 03             	add    $0x3,%eax
    60d7:	38 d0                	cmp    %dl,%al
    60d9:	7c 08                	jl     60e3 <main+0x1653>
    60db:	84 d2                	test   %dl,%dl
    60dd:	0f 85 d4 16 00 00    	jne    77b7 <main+0x2d27>
  thread_data[timer_threadi].task_count = total_barrier_count;
    60e3:	49 8d bb 40 09 00 00 	lea    0x940(%r11),%rdi
  thread_data[timer_threadi].running = 1;
    60ea:	41 c7 83 44 09 00 00 01 00 00 00 	movl   $0x1,0x944(%r11)
  thread_data[timer_threadi].task_count = total_barrier_count;
    60f5:	48 89 f8             	mov    %rdi,%rax
    60f8:	48 c1 e8 03          	shr    $0x3,%rax
    60fc:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    6103:	84 c0                	test   %al,%al
    6105:	74 08                	je     610f <main+0x167f>
    6107:	3c 03                	cmp    $0x3,%al
    6109:	0f 8e a3 16 00 00    	jle    77b2 <main+0x2d22>
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    610f:	bf 10 00 00 00       	mov    $0x10,%edi
    6114:	be 08 00 00 00       	mov    $0x8,%esi
  thread_data[timer_threadi].task_count = total_barrier_count;
    6119:	4c 89 1c 24          	mov    %r11,(%rsp)
    611d:	41 c7 83 40 09 00 00 03 00 00 00 	movl   $0x3,0x940(%r11)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    6128:	e8 33 e3 ff ff       	call   4460 <calloc@plt>
    my_thread_data[n] = &thread_data[n]; 
    612d:	4c 8b 1c 24          	mov    (%rsp),%r11
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    6131:	48 89 c7             	mov    %rax,%rdi
    my_thread_data[n] = &thread_data[n]; 
    6134:	48 c1 e8 03          	shr    $0x3,%rax
    6138:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    613f:	0f 85 e8 13 00 00    	jne    752d <main+0x2a9d>
    6145:	48 8d 47 08          	lea    0x8(%rdi),%rax
    6149:	4c 89 1f             	mov    %r11,(%rdi)
    614c:	48 89 c2             	mov    %rax,%rdx
    614f:	48 c1 ea 03          	shr    $0x3,%rdx
    6153:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    615a:	0f 85 c5 13 00 00    	jne    7525 <main+0x2a95>
    6160:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6165:	49 8d 93 80 01 00 00 	lea    0x180(%r11),%rdx
    616c:	48 89 47 08          	mov    %rax,0x8(%rdi)
    6170:	48 8d 47 10          	lea    0x10(%rdi),%rax
    6174:	48 89 c1             	mov    %rax,%rcx
    6177:	48 c1 e9 03          	shr    $0x3,%rcx
    617b:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    6182:	0f 85 ca 15 00 00    	jne    7752 <main+0x2cc2>
    6188:	48 8d 47 18          	lea    0x18(%rdi),%rax
    618c:	48 89 57 10          	mov    %rdx,0x10(%rdi)
    6190:	49 8d 93 40 02 00 00 	lea    0x240(%r11),%rdx
    6197:	48 89 c1             	mov    %rax,%rcx
    619a:	48 c1 e9 03          	shr    $0x3,%rcx
    619e:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    61a5:	0f 85 9f 15 00 00    	jne    774a <main+0x2cba>
    61ab:	48 8d 47 20          	lea    0x20(%rdi),%rax
    61af:	48 89 57 18          	mov    %rdx,0x18(%rdi)
    61b3:	49 8d 93 00 03 00 00 	lea    0x300(%r11),%rdx
    61ba:	48 89 c1             	mov    %rax,%rcx
    61bd:	48 c1 e9 03          	shr    $0x3,%rcx
    61c1:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    61c8:	0f 85 74 15 00 00    	jne    7742 <main+0x2cb2>
    61ce:	48 8d 47 28          	lea    0x28(%rdi),%rax
    61d2:	48 89 57 20          	mov    %rdx,0x20(%rdi)
    61d6:	49 8d 93 c0 03 00 00 	lea    0x3c0(%r11),%rdx
    61dd:	48 89 c1             	mov    %rax,%rcx
    61e0:	48 c1 e9 03          	shr    $0x3,%rcx
    61e4:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    61eb:	0f 85 49 15 00 00    	jne    773a <main+0x2caa>
    61f1:	48 8d 47 30          	lea    0x30(%rdi),%rax
    61f5:	48 89 57 28          	mov    %rdx,0x28(%rdi)
    61f9:	49 8d 93 80 04 00 00 	lea    0x480(%r11),%rdx
    6200:	48 89 c1             	mov    %rax,%rcx
    6203:	48 c1 e9 03          	shr    $0x3,%rcx
    6207:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    620e:	0f 85 1e 15 00 00    	jne    7732 <main+0x2ca2>
    6214:	48 8d 47 38          	lea    0x38(%rdi),%rax
    6218:	48 89 57 30          	mov    %rdx,0x30(%rdi)
    621c:	49 8d 93 40 05 00 00 	lea    0x540(%r11),%rdx
    6223:	48 89 c1             	mov    %rax,%rcx
    6226:	48 c1 e9 03          	shr    $0x3,%rcx
    622a:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    6231:	0f 85 f3 14 00 00    	jne    772a <main+0x2c9a>
    6237:	48 8d 47 40          	lea    0x40(%rdi),%rax
    623b:	48 89 57 38          	mov    %rdx,0x38(%rdi)
    623f:	49 8d 93 00 06 00 00 	lea    0x600(%r11),%rdx
    6246:	48 89 c1             	mov    %rax,%rcx
    6249:	48 c1 e9 03          	shr    $0x3,%rcx
    624d:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    6254:	0f 85 c8 14 00 00    	jne    7722 <main+0x2c92>
    625a:	48 8d 47 48          	lea    0x48(%rdi),%rax
    625e:	48 89 57 40          	mov    %rdx,0x40(%rdi)
    6262:	49 8d 93 c0 06 00 00 	lea    0x6c0(%r11),%rdx
    6269:	48 89 c1             	mov    %rax,%rcx
    626c:	48 c1 e9 03          	shr    $0x3,%rcx
    6270:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    6277:	0f 85 9d 14 00 00    	jne    771a <main+0x2c8a>
    627d:	48 8d 47 50          	lea    0x50(%rdi),%rax
    6281:	48 89 57 48          	mov    %rdx,0x48(%rdi)
    6285:	49 8d 93 80 07 00 00 	lea    0x780(%r11),%rdx
    628c:	48 89 c1             	mov    %rax,%rcx
    628f:	48 c1 e9 03          	shr    $0x3,%rcx
    6293:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    629a:	0f 85 7d 12 00 00    	jne    751d <main+0x2a8d>
    62a0:	48 8d 47 58          	lea    0x58(%rdi),%rax
    62a4:	48 89 57 50          	mov    %rdx,0x50(%rdi)
    62a8:	49 8d 93 40 08 00 00 	lea    0x840(%r11),%rdx
    62af:	48 89 c1             	mov    %rax,%rcx
    62b2:	48 c1 e9 03          	shr    $0x3,%rcx
    62b6:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    62bd:	0f 85 52 12 00 00    	jne    7515 <main+0x2a85>
  thread_data[timer_threadi].threads = my_thread_data;
    62c3:	49 8d 83 18 09 00 00 	lea    0x918(%r11),%rax
    my_thread_data[n] = &thread_data[n]; 
    62ca:	48 89 57 58          	mov    %rdx,0x58(%rdi)
  thread_data[timer_threadi].threads = my_thread_data;
    62ce:	48 89 c2             	mov    %rax,%rdx
    62d1:	48 c1 ea 03          	shr    $0x3,%rdx
    62d5:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    62dc:	0f 85 01 13 00 00    	jne    75e3 <main+0x2b53>
    62e2:	49 89 bb 18 09 00 00 	mov    %rdi,0x918(%r11)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    62e9:	49 8d bb 28 09 00 00 	lea    0x928(%r11),%rdi
    62f0:	48 89 f8             	mov    %rdi,%rax
    62f3:	48 c1 e8 03          	shr    $0x3,%rax
    62f7:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    62fe:	84 c0                	test   %al,%al
    6300:	74 08                	je     630a <main+0x187a>
    6302:	3c 03                	cmp    $0x3,%al
    6304:	0f 8e a3 14 00 00    	jle    77ad <main+0x2d1d>
  thread_data[timer_threadi].my_thread_count = 2;
    630a:	49 8d bb 30 09 00 00 	lea    0x930(%r11),%rdi
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    6311:	41 c7 83 28 09 00 00 0c 00 00 00 	movl   $0xc,0x928(%r11)
  thread_data[timer_threadi].my_thread_count = 2;
    631c:	48 89 f8             	mov    %rdi,%rax
    631f:	48 c1 e8 03          	shr    $0x3,%rax
    6323:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    632a:	84 c0                	test   %al,%al
    632c:	74 08                	je     6336 <main+0x18a6>
    632e:	3c 03                	cmp    $0x3,%al
    6330:	0f 8e 72 14 00 00    	jle    77a8 <main+0x2d18>
  thread_data[timer_threadi].thread_index = 0;
    6336:	49 8d bb 04 09 00 00 	lea    0x904(%r11),%rdi
  thread_data[timer_threadi].my_thread_count = 2;
    633d:	41 c7 83 30 09 00 00 02 00 00 00 	movl   $0x2,0x930(%r11)
  thread_data[timer_threadi].thread_index = 0;
    6348:	48 89 f8             	mov    %rdi,%rax
    634b:	48 c1 e8 03          	shr    $0x3,%rax
    634f:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    6356:	48 89 f8             	mov    %rdi,%rax
    6359:	83 e0 07             	and    $0x7,%eax
    635c:	83 c0 03             	add    $0x3,%eax
    635f:	38 d0                	cmp    %dl,%al
    6361:	7c 08                	jl     636b <main+0x18db>
    6363:	84 d2                	test   %dl,%dl
    6365:	0f 85 ce 14 00 00    	jne    7839 <main+0x2da9>
    636b:	ba 0c 00 00 00       	mov    $0xc,%edx
    6370:	48 8d 35 49 b3 00 00 	lea    0xb349(%rip),%rsi        # 116c0 <_IO_stdin_used+0x16c0>
    6377:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    6379:	31 ed                	xor    %ebp,%ebp
    637b:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[timer_threadi].thread_index = 0;
    6380:	4c 89 1c 24          	mov    %r11,(%rsp)
    6384:	41 89 ed             	mov    %ebp,%r13d
    6387:	41 c7 83 04 09 00 00 00 00 00 00 	movl   $0x0,0x904(%r11)
    6392:	e8 89 e1 ff ff       	call   4520 <__printf_chk@plt>
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    6397:	4c 8b 1c 24          	mov    (%rsp),%r11
    639b:	48 8d 15 1e 1d 00 00 	lea    0x1d1e(%rip),%rdx        # 80c0 <timer_thread>
    63a2:	49 8d b4 24 a0 02 00 00 	lea    0x2a0(%r12),%rsi
    63aa:	48 8d 7b 60          	lea    0x60(%rbx),%rdi
    63ae:	49 8d 8b 00 09 00 00 	lea    0x900(%r11),%rcx
    63b5:	e8 96 e2 ff ff       	call   4650 <pthread_create@plt>
    63ba:	4c 8b 1c 24          	mov    (%rsp),%r11
    63be:	4d 89 f0             	mov    %r14,%r8
    63c1:	48 89 d9             	mov    %rbx,%rcx
    63c4:	48 89 5c 24 58       	mov    %rbx,0x58(%rsp)
    63c9:	41 be 02 00 00 00    	mov    $0x2,%r14d
    63cf:	4c 89 5c 24 60       	mov    %r11,0x60(%rsp)
    63d4:	4c 89 da             	mov    %r11,%rdx
    63d7:	4c 89 7c 24 68       	mov    %r15,0x68(%rsp)
    63dc:	48 89 5c 24 70       	mov    %rbx,0x70(%rsp)
    for (int d = 0 ; d < threads_per_group ; d++) {
    63e1:	48 89 14 24          	mov    %rdx,(%rsp)
    63e5:	47 8d 7c 2d 00       	lea    0x0(%r13,%r13,1),%r15d
  int curcpu = 0;
    63ea:	4c 89 c5             	mov    %r8,%rbp
    63ed:	49 89 cc             	mov    %rcx,%r12
    63f0:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    63f5:	48 89 d3             	mov    %rdx,%rbx
    63f8:	4c 89 44 24 10       	mov    %r8,0x10(%rsp)
      thread_data[x].type = WORKER;
    63fd:	48 8d 7b 0c          	lea    0xc(%rbx),%rdi
    6401:	48 89 f8             	mov    %rdi,%rax
    6404:	48 c1 e8 03          	shr    $0x3,%rax
    6408:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    640f:	48 89 f8             	mov    %rdi,%rax
    6412:	83 e0 07             	and    $0x7,%eax
    6415:	83 c0 03             	add    $0x3,%eax
    6418:	38 d0                	cmp    %dl,%al
    641a:	7c 08                	jl     6424 <main+0x1994>
    641c:	84 d2                	test   %dl,%dl
    641e:	0f 85 f1 12 00 00    	jne    7715 <main+0x2c85>
      thread_data[x].running = 1;
    6424:	48 8d 7b 44          	lea    0x44(%rbx),%rdi
      thread_data[x].type = WORKER;
    6428:	c7 43 0c 01 00 00 00 	movl   $0x1,0xc(%rbx)
      thread_data[x].running = 1;
    642f:	48 89 f8             	mov    %rdi,%rax
    6432:	48 c1 e8 03          	shr    $0x3,%rax
    6436:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    643d:	48 89 f8             	mov    %rdi,%rax
    6440:	83 e0 07             	and    $0x7,%eax
    6443:	83 c0 03             	add    $0x3,%eax
    6446:	38 d0                	cmp    %dl,%al
    6448:	7c 08                	jl     6452 <main+0x19c2>
    644a:	84 d2                	test   %dl,%dl
    644c:	0f 85 be 12 00 00    	jne    7710 <main+0x2c80>
    6452:	c7 43 44 01 00 00 00 	movl   $0x1,0x44(%rbx)
    6459:	44 89 e9             	mov    %r13d,%ecx
    645c:	44 89 fa             	mov    %r15d,%edx
    645f:	31 c0                	xor    %eax,%eax
    6461:	48 8d 35 98 b2 00 00 	lea    0xb298(%rip),%rsi        # 11700 <_IO_stdin_used+0x1700>
    6468:	bf 01 00 00 00       	mov    $0x1,%edi
    646d:	e8 ae e0 ff ff       	call   4520 <__printf_chk@plt>
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    6472:	4c 89 e7             	mov    %r12,%rdi
    6475:	48 89 d9             	mov    %rbx,%rcx
    6478:	48 89 ee             	mov    %rbp,%rsi
    647b:	48 8d 15 fe 6f 00 00 	lea    0x6ffe(%rip),%rdx        # d480 <barriered_thread>
    6482:	e8 c9 e1 ff ff       	call   4650 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    6487:	48 8d bb b0 00 00 00 	lea    0xb0(%rbx),%rdi
    648e:	48 89 f8             	mov    %rdi,%rax
    6491:	48 c1 e8 03          	shr    $0x3,%rax
    6495:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    649c:	0f 85 69 12 00 00    	jne    770b <main+0x2c7b>
    64a2:	4c 89 e0             	mov    %r12,%rax
    64a5:	48 8b 93 b0 00 00 00 	mov    0xb0(%rbx),%rdx
    64ac:	48 c1 e8 03          	shr    $0x3,%rax
    64b0:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    64b7:	0f 85 46 12 00 00    	jne    7703 <main+0x2c73>
    64bd:	49 8b 3c 24          	mov    (%r12),%rdi
    for (int d = 0 ; d < threads_per_group ; d++) {
    64c1:	41 83 c7 01          	add    $0x1,%r15d
    64c5:	49 83 c4 08          	add    $0x8,%r12
    64c9:	48 83 c5 38          	add    $0x38,%rbp
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    64cd:	be 08 00 00 00       	mov    $0x8,%esi
    for (int d = 0 ; d < threads_per_group ; d++) {
    64d2:	48 81 c3 c0 00 00 00 	add    $0xc0,%rbx
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    64d9:	e8 62 df ff ff       	call   4440 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    64de:	45 39 f7             	cmp    %r14d,%r15d
    64e1:	0f 85 16 ff ff ff    	jne    63fd <main+0x196d>
  for (int k = 0 ; k < group_count ; k++) {
    64e7:	48 8b 14 24          	mov    (%rsp),%rdx
    64eb:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    64f0:	41 83 c5 01          	add    $0x1,%r13d
    64f4:	45 8d 77 02          	lea    0x2(%r15),%r14d
    64f8:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    64fd:	48 81 c2 80 01 00 00 	add    $0x180,%rdx
    6504:	48 83 c1 10          	add    $0x10,%rcx
    6508:	49 83 c0 70          	add    $0x70,%r8
    650c:	41 83 fd 06          	cmp    $0x6,%r13d
    6510:	0f 85 cb fe ff ff    	jne    63e1 <main+0x1951>
    thread_data[x].type = IO;
    6516:	4c 8b 5c 24 60       	mov    0x60(%rsp),%r11
    651b:	4c 8b 6c 24 58       	mov    0x58(%rsp),%r13
    6520:	4c 8b 7c 24 68       	mov    0x68(%rsp),%r15
    6525:	48 8b 5c 24 70       	mov    0x70(%rsp),%rbx
    652a:	49 8d bb cc 09 00 00 	lea    0x9cc(%r11),%rdi
    6531:	48 89 f8             	mov    %rdi,%rax
    6534:	48 c1 e8 03          	shr    $0x3,%rax
    6538:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    653f:	48 89 f8             	mov    %rdi,%rax
    6542:	83 e0 07             	and    $0x7,%eax
    6545:	83 c0 03             	add    $0x3,%eax
    6548:	38 d0                	cmp    %dl,%al
    654a:	7c 08                	jl     6554 <main+0x1ac4>
    654c:	84 d2                	test   %dl,%dl
    654e:	0f 85 e0 12 00 00    	jne    7834 <main+0x2da4>
    thread_data[x].running = 1;
    6554:	49 8d bb 04 0a 00 00 	lea    0xa04(%r11),%rdi
    thread_data[x].type = IO;
    655b:	41 c7 83 cc 09 00 00 02 00 00 00 	movl   $0x2,0x9cc(%r11)
    thread_data[x].running = 1;
    6566:	48 89 f8             	mov    %rdi,%rax
    6569:	48 c1 e8 03          	shr    $0x3,%rax
    656d:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    6574:	48 89 f8             	mov    %rdi,%rax
    6577:	83 e0 07             	and    $0x7,%eax
    657a:	83 c0 03             	add    $0x3,%eax
    657d:	38 d0                	cmp    %dl,%al
    657f:	7c 08                	jl     6589 <main+0x1af9>
    6581:	84 d2                	test   %dl,%dl
    6583:	0f 85 a6 12 00 00    	jne    782f <main+0x2d9f>
    6589:	41 c7 83 04 0a 00 00 01 00 00 00 	movl   $0x1,0xa04(%r11)
    thread_data[x].task_count = 0;
    6594:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    6599:	48 c1 e8 03          	shr    $0x3,%rax
    659d:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    65a4:	84 c0                	test   %al,%al
    65a6:	74 08                	je     65b0 <main+0x1b20>
    65a8:	3c 03                	cmp    $0x3,%al
    65aa:	0f 8e 75 12 00 00    	jle    7825 <main+0x2d95>
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    65b0:	bf 01 00 00 00       	mov    $0x1,%edi
    65b5:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].task_count = 0;
    65ba:	4c 89 1c 24          	mov    %r11,(%rsp)
    65be:	41 c7 83 00 0a 00 00 00 00 00 00 	movl   $0x0,0xa00(%r11)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    65c9:	e8 92 de ff ff       	call   4460 <calloc@plt>
    65ce:	4c 8b 1c 24          	mov    (%rsp),%r11
    65d2:	49 8d bb 18 0a 00 00 	lea    0xa18(%r11),%rdi
    65d9:	48 89 fa             	mov    %rdi,%rdx
    65dc:	48 c1 ea 03          	shr    $0x3,%rdx
    65e0:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    65e7:	0f 85 ff 10 00 00    	jne    76ec <main+0x2c5c>
    65ed:	49 89 83 18 0a 00 00 	mov    %rax,0xa18(%r11)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    65f4:	31 ff                	xor    %edi,%edi
    65f6:	be 00 08 00 00       	mov    $0x800,%esi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    65fb:	4c 89 1c 24          	mov    %r11,(%rsp)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    65ff:	e8 cc df ff ff       	call   45d0 <eventfd@plt>
    6604:	4c 8b 1c 24          	mov    (%rsp),%r11
    6608:	49 8d bb 20 0a 00 00 	lea    0xa20(%r11),%rdi
    660f:	48 89 fa             	mov    %rdi,%rdx
    6612:	48 c1 ea 03          	shr    $0x3,%rdx
    6616:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    661d:	84 d2                	test   %dl,%dl
    661f:	74 09                	je     662a <main+0x1b9a>
    6621:	80 fa 03             	cmp    $0x3,%dl
    6624:	0f 8e f6 11 00 00    	jle    7820 <main+0x2d90>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    662a:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    662f:	41 89 83 20 0a 00 00 	mov    %eax,0xa20(%r11)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    6636:	be 08 00 00 00       	mov    $0x8,%esi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    663b:	4c 89 1c 24          	mov    %r11,(%rsp)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    663f:	e8 1c de ff ff       	call   4460 <calloc@plt>
      my_thread_data[n] = &thread_data[n]; 
    6644:	4c 8b 1c 24          	mov    (%rsp),%r11
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    6648:	48 89 c7             	mov    %rax,%rdi
      my_thread_data[n] = &thread_data[n]; 
    664b:	48 c1 e8 03          	shr    $0x3,%rax
    664f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6656:	0f 85 8b 10 00 00    	jne    76e7 <main+0x2c57>
    665c:	48 8d 47 08          	lea    0x8(%rdi),%rax
    6660:	4c 89 1f             	mov    %r11,(%rdi)
    6663:	48 89 c2             	mov    %rax,%rdx
    6666:	48 c1 ea 03          	shr    $0x3,%rdx
    666a:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    6671:	0f 85 84 10 00 00    	jne    76fb <main+0x2c6b>
    6677:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    667c:	48 89 47 08          	mov    %rax,0x8(%rdi)
    thread_data[x].threads = my_thread_data;
    6680:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    6685:	48 c1 e8 03          	shr    $0x3,%rax
    6689:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6690:	0f 85 5b 10 00 00    	jne    76f1 <main+0x2c61>
    thread_data[x].thread_count = thread_count;
    6696:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    thread_data[x].threads = my_thread_data;
    669b:	49 89 bb d8 09 00 00 	mov    %rdi,0x9d8(%r11)
    thread_data[x].thread_count = thread_count;
    66a2:	48 c1 e8 03          	shr    $0x3,%rax
    66a6:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    66ad:	84 c0                	test   %al,%al
    66af:	74 08                	je     66b9 <main+0x1c29>
    66b1:	3c 03                	cmp    $0x3,%al
    66b3:	0f 8e 5d 11 00 00    	jle    7816 <main+0x2d86>
    66b9:	41 c7 83 e8 09 00 00 02 00 00 00 	movl   $0x2,0x9e8(%r11)
    thread_data[x].thread_index = x;
    66c4:	4c 89 f8             	mov    %r15,%rax
    66c7:	48 c1 e8 03          	shr    $0x3,%rax
    66cb:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    66d2:	4c 89 f8             	mov    %r15,%rax
    66d5:	83 e0 07             	and    $0x7,%eax
    66d8:	83 c0 03             	add    $0x3,%eax
    66db:	38 d0                	cmp    %dl,%al
    66dd:	7c 08                	jl     66e7 <main+0x1c57>
    66df:	84 d2                	test   %dl,%dl
    66e1:	0f 85 27 11 00 00    	jne    780e <main+0x2d7e>
    66e7:	ba 0d 00 00 00       	mov    $0xd,%edx
    66ec:	bf 01 00 00 00       	mov    $0x1,%edi
    66f1:	31 c0                	xor    %eax,%eax
    66f3:	4c 89 1c 24          	mov    %r11,(%rsp)
    66f7:	41 c7 83 c4 09 00 00 0d 00 00 00 	movl   $0xd,0x9c4(%r11)
    6702:	48 8d 35 57 b0 00 00 	lea    0xb057(%rip),%rsi        # 11760 <_IO_stdin_used+0x1760>
    6709:	4c 8d 73 70          	lea    0x70(%rbx),%r14
    670d:	e8 0e de ff ff       	call   4520 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    6712:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
    6717:	48 8d 7b 68          	lea    0x68(%rbx),%rdi
    671b:	48 8b 4c 24 38       	mov    0x38(%rsp),%rcx
    6720:	48 8d 15 39 50 00 00 	lea    0x5039(%rip),%rdx        # b760 <io_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    6727:	bb 0e 00 00 00       	mov    $0xe,%ebx
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    672c:	48 81 c6 d8 02 00 00 	add    $0x2d8,%rsi
    6733:	e8 18 df ff ff       	call   4650 <pthread_create@plt>
    6738:	ba 0e 00 00 00       	mov    $0xe,%edx
    673d:	48 8d 35 5c b0 00 00 	lea    0xb05c(%rip),%rsi        # 117a0 <_IO_stdin_used+0x17a0>
    6744:	31 c0                	xor    %eax,%eax
    6746:	bf 01 00 00 00       	mov    $0x1,%edi
    674b:	e8 d0 dd ff ff       	call   4520 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    6750:	4c 8b 1c 24          	mov    (%rsp),%r11
    6754:	4c 8b 7c 24 50       	mov    0x50(%rsp),%r15
    6759:	4d 8d a3 8c 0a 00 00 	lea    0xa8c(%r11),%r12
    6760:	49 81 c7 10 03 00 00 	add    $0x310,%r15
    6767:	4c 89 e5             	mov    %r12,%rbp
    676a:	4d 89 dc             	mov    %r11,%r12
    676d:	89 da                	mov    %ebx,%edx
    676f:	48 8d 35 6a b0 00 00 	lea    0xb06a(%rip),%rsi        # 117e0 <_IO_stdin_used+0x17e0>
    6776:	bf 01 00 00 00       	mov    $0x1,%edi
    677b:	31 c0                	xor    %eax,%eax
    677d:	e8 9e dd ff ff       	call   4520 <__printf_chk@plt>
    thread_data[x].type = EXTERNAL;
    6782:	48 8d 45 f4          	lea    -0xc(%rbp),%rax
    6786:	48 89 04 24          	mov    %rax,(%rsp)
    678a:	48 89 e8             	mov    %rbp,%rax
    678d:	48 c1 e8 03          	shr    $0x3,%rax
    6791:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    6798:	48 89 e8             	mov    %rbp,%rax
    679b:	83 e0 07             	and    $0x7,%eax
    679e:	83 c0 03             	add    $0x3,%eax
    67a1:	38 d0                	cmp    %dl,%al
    67a3:	7c 08                	jl     67ad <main+0x1d1d>
    67a5:	84 d2                	test   %dl,%dl
    67a7:	0f 85 59 10 00 00    	jne    7806 <main+0x2d76>
    thread_data[x].running = 1;
    67ad:	48 8d 7d 38          	lea    0x38(%rbp),%rdi
    thread_data[x].type = EXTERNAL;
    67b1:	c7 45 00 03 00 00 00 	movl   $0x3,0x0(%rbp)
    thread_data[x].running = 1;
    67b8:	48 89 f8             	mov    %rdi,%rax
    67bb:	48 c1 e8 03          	shr    $0x3,%rax
    67bf:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    67c6:	48 89 f8             	mov    %rdi,%rax
    67c9:	83 e0 07             	and    $0x7,%eax
    67cc:	83 c0 03             	add    $0x3,%eax
    67cf:	38 d0                	cmp    %dl,%al
    67d1:	7c 08                	jl     67db <main+0x1d4b>
    67d3:	84 d2                	test   %dl,%dl
    67d5:	0f 85 26 10 00 00    	jne    7801 <main+0x2d71>
    thread_data[x].task_count = 0;
    67db:	48 8d 7d 34          	lea    0x34(%rbp),%rdi
    thread_data[x].running = 1;
    67df:	c7 45 38 01 00 00 00 	movl   $0x1,0x38(%rbp)
    thread_data[x].task_count = 0;
    67e6:	48 89 f8             	mov    %rdi,%rax
    67e9:	48 c1 e8 03          	shr    $0x3,%rax
    67ed:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    67f4:	84 c0                	test   %al,%al
    67f6:	74 08                	je     6800 <main+0x1d70>
    67f8:	3c 03                	cmp    $0x3,%al
    67fa:	0f 8e fc 0f 00 00    	jle    77fc <main+0x2d6c>
    6800:	c7 45 34 00 00 00 00 	movl   $0x0,0x34(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    6807:	bf 01 00 00 00       	mov    $0x1,%edi
    680c:	be 08 00 00 00       	mov    $0x8,%esi
    6811:	e8 4a dc ff ff       	call   4460 <calloc@plt>
    6816:	48 89 c7             	mov    %rax,%rdi
    6819:	48 8d 45 44          	lea    0x44(%rbp),%rax
    681d:	48 89 c2             	mov    %rax,%rdx
    6820:	48 c1 ea 03          	shr    $0x3,%rdx
    6824:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    682b:	0f 85 c3 0f 00 00    	jne    77f4 <main+0x2d64>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    6831:	48 89 f8             	mov    %rdi,%rax
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    6834:	48 89 7d 44          	mov    %rdi,0x44(%rbp)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    6838:	48 c1 e8 03          	shr    $0x3,%rax
    683c:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6843:	0f 85 a6 0f 00 00    	jne    77ef <main+0x2d5f>
    6849:	48 8b 84 24 a0 00 00 00 	mov    0xa0(%rsp),%rax
    6851:	48 89 07             	mov    %rax,(%rdi)
	  thread_data[x].buffers_count = 1;
    6854:	48 8d bd b0 00 00 00 	lea    0xb0(%rbp),%rdi
    685b:	48 89 f8             	mov    %rdi,%rax
    685e:	48 c1 e8 03          	shr    $0x3,%rax
    6862:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    6869:	48 89 f8             	mov    %rdi,%rax
    686c:	83 e0 07             	and    $0x7,%eax
    686f:	83 c0 03             	add    $0x3,%eax
    6872:	38 d0                	cmp    %dl,%al
    6874:	7c 08                	jl     687e <main+0x1dee>
    6876:	84 d2                	test   %dl,%dl
    6878:	0f 85 6c 0f 00 00    	jne    77ea <main+0x2d5a>
    687e:	c7 85 b0 00 00 00 01 00 00 00 	movl   $0x1,0xb0(%rbp)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    6888:	bf 02 00 00 00       	mov    $0x2,%edi
    688d:	be 08 00 00 00       	mov    $0x8,%esi
    6892:	e8 c9 db ff ff       	call   4460 <calloc@plt>
    6897:	48 89 c7             	mov    %rax,%rdi
      my_thread_data[n] = &thread_data[n]; 
    689a:	48 c1 e8 03          	shr    $0x3,%rax
    689e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    68a5:	0f 85 3a 0f 00 00    	jne    77e5 <main+0x2d55>
    68ab:	48 8d 47 08          	lea    0x8(%rdi),%rax
    68af:	4c 89 27             	mov    %r12,(%rdi)
    68b2:	48 89 c2             	mov    %rax,%rdx
    68b5:	48 c1 ea 03          	shr    $0x3,%rdx
    68b9:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    68c0:	0f 85 17 0f 00 00    	jne    77dd <main+0x2d4d>
    68c6:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    68cb:	48 89 47 08          	mov    %rax,0x8(%rdi)
    thread_data[x].threads = my_thread_data;
    68cf:	48 8d 45 0c          	lea    0xc(%rbp),%rax
    68d3:	48 89 c2             	mov    %rax,%rdx
    68d6:	48 c1 ea 03          	shr    $0x3,%rdx
    68da:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    68e1:	0f 85 ee 0e 00 00    	jne    77d5 <main+0x2d45>
    68e7:	48 89 7d 0c          	mov    %rdi,0xc(%rbp)
    thread_data[x].thread_count = thread_count;
    68eb:	48 8d 7d 1c          	lea    0x1c(%rbp),%rdi
    68ef:	48 89 f8             	mov    %rdi,%rax
    68f2:	48 c1 e8 03          	shr    $0x3,%rax
    68f6:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    68fd:	84 c0                	test   %al,%al
    68ff:	74 08                	je     6909 <main+0x1e79>
    6901:	3c 03                	cmp    $0x3,%al
    6903:	0f 8e 1d 10 00 00    	jle    7926 <main+0x2e96>
    thread_data[x].total_thread_count = total_threads;
    6909:	48 8d 7d 20          	lea    0x20(%rbp),%rdi
    thread_data[x].thread_count = thread_count;
    690d:	c7 45 1c 02 00 00 00 	movl   $0x2,0x1c(%rbp)
    thread_data[x].total_thread_count = total_threads;
    6914:	48 89 f8             	mov    %rdi,%rax
    6917:	48 c1 e8 03          	shr    $0x3,%rax
    691b:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    6922:	48 89 f8             	mov    %rdi,%rax
    6925:	83 e0 07             	and    $0x7,%eax
    6928:	83 c0 03             	add    $0x3,%eax
    692b:	38 d0                	cmp    %dl,%al
    692d:	7c 08                	jl     6937 <main+0x1ea7>
    692f:	84 d2                	test   %dl,%dl
    6931:	0f 85 ea 0f 00 00    	jne    7921 <main+0x2e91>
    thread_data[x].thread_index = x;
    6937:	48 8d 7d f8          	lea    -0x8(%rbp),%rdi
    thread_data[x].total_thread_count = total_threads;
    693b:	c7 45 20 10 00 00 00 	movl   $0x10,0x20(%rbp)
    thread_data[x].thread_index = x;
    6942:	48 89 f8             	mov    %rdi,%rax
    6945:	48 c1 e8 03          	shr    $0x3,%rax
    6949:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    6950:	48 89 f8             	mov    %rdi,%rax
    6953:	83 e0 07             	and    $0x7,%eax
    6956:	83 c0 03             	add    $0x3,%eax
    6959:	38 d0                	cmp    %dl,%al
    695b:	7c 08                	jl     6965 <main+0x1ed5>
    695d:	84 d2                	test   %dl,%dl
    695f:	0f 85 b7 0f 00 00    	jne    791c <main+0x2e8c>
    6965:	89 5d f8             	mov    %ebx,-0x8(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    6968:	48 8b 0c 24          	mov    (%rsp),%rcx
    696c:	4c 89 fe             	mov    %r15,%rsi
    696f:	4c 89 f7             	mov    %r14,%rdi
    6972:	48 8d 15 b7 13 00 00 	lea    0x13b7(%rip),%rdx        # 7d30 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    6979:	48 81 c5 c0 00 00 00 	add    $0xc0,%rbp
    6980:	49 83 c6 08          	add    $0x8,%r14
    6984:	49 83 c7 38          	add    $0x38,%r15
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    6988:	e8 c3 dc ff ff       	call   4650 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    698d:	48 83 84 24 a0 00 00 00 10 	addq   $0x10,0xa0(%rsp)
    6996:	83 fb 0e             	cmp    $0xe,%ebx
    6999:	75 0a                	jne    69a5 <main+0x1f15>
    699b:	bb 0f 00 00 00       	mov    $0xf,%ebx
    69a0:	e9 c8 fd ff ff       	jmp    676d <main+0x1cdd>
    69a5:	4d 89 e3             	mov    %r12,%r11
    69a8:	4d 8d 74 24 08       	lea    0x8(%r12),%r14
    69ad:	48 8d 1d 6c ae 00 00 	lea    0xae6c(%rip),%rbx        # 11820 <_IO_stdin_used+0x1820>
    69b4:	4d 8d a4 24 08 0c 00 00 	lea    0xc08(%r12),%r12
    69bc:	4c 89 dd             	mov    %r11,%rbp
    69bf:	90                   	nop
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
    69c0:	4c 89 f0             	mov    %r14,%rax
    69c3:	48 c1 e8 03          	shr    $0x3,%rax
    69c7:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    69ce:	84 c0                	test   %al,%al
    69d0:	74 08                	je     69da <main+0x1f4a>
    69d2:	3c 03                	cmp    $0x3,%al
    69d4:	0f 8e 3a 0f 00 00    	jle    7914 <main+0x2e84>
    69da:	49 8d 7e fc          	lea    -0x4(%r14),%rdi
    69de:	41 8b 0e             	mov    (%r14),%ecx
    69e1:	48 89 f8             	mov    %rdi,%rax
    69e4:	48 c1 e8 03          	shr    $0x3,%rax
    69e8:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    69ef:	48 89 f8             	mov    %rdi,%rax
    69f2:	83 e0 07             	and    $0x7,%eax
    69f5:	83 c0 03             	add    $0x3,%eax
    69f8:	38 d0                	cmp    %dl,%al
    69fa:	7c 08                	jl     6a04 <main+0x1f74>
    69fc:	84 d2                	test   %dl,%dl
    69fe:	0f 85 0b 0f 00 00    	jne    790f <main+0x2e7f>
    6a04:	41 8b 56 fc          	mov    -0x4(%r14),%edx
    6a08:	48 89 de             	mov    %rbx,%rsi
    6a0b:	bf 01 00 00 00       	mov    $0x1,%edi
    6a10:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    6a12:	49 81 c6 c0 00 00 00 	add    $0xc0,%r14
    6a19:	e8 02 db ff ff       	call   4520 <__printf_chk@plt>
    6a1e:	4d 39 f4             	cmp    %r14,%r12
    6a21:	75 9d                	jne    69c0 <main+0x1f30>
    6a23:	48 8d 3d 36 ae 00 00 	lea    0xae36(%rip),%rdi        # 11860 <_IO_stdin_used+0x1860>
    6a2a:	48 89 2c 24          	mov    %rbp,(%rsp)
  for (int x = 0 ; x < total_threads ; x++) {
    6a2e:	31 db                	xor    %ebx,%ebx
    6a30:	4c 8d 25 69 ae 00 00 	lea    0xae69(%rip),%r12        # 118a0 <_IO_stdin_used+0x18a0>
    6a37:	e8 c4 dd ff ff       	call   4800 <puts@plt>
    6a3c:	48 8b 84 24 b8 00 00 00 	mov    0xb8(%rsp),%rax
    6a44:	4c 8b 34 24          	mov    (%rsp),%r14
    6a48:	4c 8d 78 c0          	lea    -0x40(%rax),%r15
    6a4c:	0f 1f 40 00          	nopl   0x0(%rax)
    void * result; 
    6a50:	4c 89 fd             	mov    %r15,%rbp
    pthread_join(thread[x], &result);
    6a53:	4c 89 e8             	mov    %r13,%rax
    void * result; 
    6a56:	48 c1 ed 03          	shr    $0x3,%rbp
    pthread_join(thread[x], &result);
    6a5a:	48 c1 e8 03          	shr    $0x3,%rax
    void * result; 
    6a5e:	c6 85 00 80 ff 7f 00 	movb   $0x0,0x7fff8000(%rbp)
    pthread_join(thread[x], &result);
    6a65:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6a6c:	0f 85 95 0e 00 00    	jne    7907 <main+0x2e77>
    6a72:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    6a76:	4c 89 fe             	mov    %r15,%rsi
  for (int x = 0 ; x < total_threads ; x++) {
    6a79:	49 83 c5 08          	add    $0x8,%r13
    pthread_join(thread[x], &result);
    6a7d:	e8 ae dd ff ff       	call   4830 <pthread_join@plt>
    6a82:	89 da                	mov    %ebx,%edx
    6a84:	4c 89 e6             	mov    %r12,%rsi
    6a87:	bf 01 00 00 00       	mov    $0x1,%edi
    6a8c:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    6a8e:	83 c3 01             	add    $0x1,%ebx
    6a91:	e8 8a da ff ff       	call   4520 <__printf_chk@plt>
    6a96:	c6 85 00 80 ff 7f f8 	movb   $0xf8,0x7fff8000(%rbp)
    6a9d:	83 fb 10             	cmp    $0x10,%ebx
    6aa0:	75 ae                	jne    6a50 <main+0x1fc0>
  long received = 0;
    6aa2:	45 31 d2             	xor    %r10d,%r10d
  long ingests = 0;
    6aa5:	45 31 c0             	xor    %r8d,%r8d
    6aa8:	48 8b 6c 24 40       	mov    0x40(%rsp),%rbp
    6aad:	4c 89 74 24 30       	mov    %r14,0x30(%rsp)
  for (int x = 0 ; x < thread_count ; x++) {
    6ab2:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
  long total = 0;
    6aba:	45 31 ff             	xor    %r15d,%r15d
    6abd:	4d 89 d4             	mov    %r10,%r12
    6ac0:	4d 89 c6             	mov    %r8,%r14
  long sents = 0;
    6ac3:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
  long sends = 0;
    6acc:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
    6ad5:	bf 0a 00 00 00       	mov    $0xa,%edi
    6ada:	8b 5c 24 28          	mov    0x28(%rsp),%ebx
    6ade:	e8 4d da ff ff       	call   4530 <putchar@plt>
    printf("Total Protected %ld\n", protected_state[me].protected);
    6ae3:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    6aeb:	83 f3 01             	xor    $0x1,%ebx
    6aee:	48 c1 e8 03          	shr    $0x3,%rax
    6af2:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6af9:	0f 85 fb 0d 00 00    	jne    78fa <main+0x2e6a>
    6aff:	48 8d 35 da ad 00 00 	lea    0xadda(%rip),%rsi        # 118e0 <_IO_stdin_used+0x18e0>
    6b06:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    6b0e:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    6b13:	4c 8d 6d 08          	lea    0x8(%rbp),%r13
    6b17:	48 8b 10             	mov    (%rax),%rdx
    6b1a:	31 c0                	xor    %eax,%eax
    6b1c:	e8 ff d9 ff ff       	call   4520 <__printf_chk@plt>
    6b21:	4c 89 e8             	mov    %r13,%rax
    6b24:	48 c1 e8 03          	shr    $0x3,%rax
    6b28:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    6b2f:	84 c0                	test   %al,%al
    6b31:	74 08                	je     6b3b <main+0x20ab>
    6b33:	3c 03                	cmp    $0x3,%al
    6b35:	0f 8e 51 0d 00 00    	jle    788c <main+0x2dfc>
    6b3b:	8b 45 08             	mov    0x8(%rbp),%eax
    6b3e:	85 c0                	test   %eax,%eax
    6b40:	0f 8e ea 08 00 00    	jle    7430 <main+0x29a0>
      v += thread_data[me].tasks[n].v;
    6b46:	48 89 ea             	mov    %rbp,%rdx
    6b49:	48 c1 ea 03          	shr    $0x3,%rdx
    6b4d:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    6b54:	0f 85 3f 0d 00 00    	jne    7899 <main+0x2e09>
    6b5a:	48 8b 75 00          	mov    0x0(%rbp),%rsi
    6b5e:	48 63 c8             	movslq %eax,%rcx
    long v = 0;
    6b61:	31 d2                	xor    %edx,%edx
    6b63:	48 c1 e1 09          	shl    $0x9,%rcx
    6b67:	48 8d be 10 01 00 00 	lea    0x110(%rsi),%rdi
    6b6e:	48 01 f9             	add    %rdi,%rcx
    6b71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      v += thread_data[me].tasks[n].v;
    6b78:	48 89 f8             	mov    %rdi,%rax
    6b7b:	48 c1 e8 03          	shr    $0x3,%rax
    6b7f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6b86:	0f 85 08 0d 00 00    	jne    7894 <main+0x2e04>
    6b8c:	48 03 17             	add    (%rdi),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    6b8f:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    6b96:	48 39 f9             	cmp    %rdi,%rcx
    6b99:	75 dd                	jne    6b78 <main+0x20e8>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    6b9b:	48 63 cb             	movslq %ebx,%rcx
    6b9e:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    6ba3:	48 f7 d9             	neg    %rcx
    6ba6:	81 e1 c0 00 00 00    	and    $0xc0,%ecx
    6bac:	48 01 c1             	add    %rax,%rcx
    6baf:	48 8d 79 40          	lea    0x40(%rcx),%rdi
    6bb3:	48 89 f8             	mov    %rdi,%rax
    6bb6:	48 c1 e8 03          	shr    $0x3,%rax
    6bba:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    6bc1:	84 c0                	test   %al,%al
    6bc3:	74 08                	je     6bcd <main+0x213d>
    6bc5:	3c 03                	cmp    $0x3,%al
    6bc7:	0f 8e eb 0c 00 00    	jle    78b8 <main+0x2e28>
    6bcd:	8b 41 40             	mov    0x40(%rcx),%eax
    6bd0:	85 c0                	test   %eax,%eax
    6bd2:	7e 57                	jle    6c2b <main+0x219b>
      v += thread_data[other].tasks[n].v;
    6bd4:	48 8d 79 38          	lea    0x38(%rcx),%rdi
    6bd8:	48 89 fe             	mov    %rdi,%rsi
    6bdb:	48 c1 ee 03          	shr    $0x3,%rsi
    6bdf:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    6be6:	0f 85 c7 0c 00 00    	jne    78b3 <main+0x2e23>
    6bec:	48 8b 79 38          	mov    0x38(%rcx),%rdi
    6bf0:	48 63 c8             	movslq %eax,%rcx
    6bf3:	48 c1 e1 09          	shl    $0x9,%rcx
    6bf7:	48 81 c7 10 01 00 00 	add    $0x110,%rdi
    6bfe:	48 01 f9             	add    %rdi,%rcx
    6c01:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6c08:	48 89 f8             	mov    %rdi,%rax
    6c0b:	48 c1 e8 03          	shr    $0x3,%rax
    6c0f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6c16:	0f 85 92 0c 00 00    	jne    78ae <main+0x2e1e>
    6c1c:	48 03 17             	add    (%rdi),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    6c1f:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    6c26:	48 39 f9             	cmp    %rdi,%rcx
    6c29:	75 dd                	jne    6c08 <main+0x2178>
    6c2b:	31 c0                	xor    %eax,%eax
    6c2d:	48 8d 35 ec ac 00 00 	lea    0xacec(%rip),%rsi        # 11920 <_IO_stdin_used+0x1920>
    6c34:	bf 01 00 00 00       	mov    $0x1,%edi
    6c39:	e8 e2 d8 ff ff       	call   4520 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    6c3e:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    6c46:	48 c1 e8 03          	shr    $0x3,%rax
    6c4a:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6c51:	0f 85 4a 0c 00 00    	jne    78a1 <main+0x2e11>
    6c57:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    6c5f:	48 8d 35 fa ac 00 00 	lea    0xacfa(%rip),%rsi        # 11960 <_IO_stdin_used+0x1960>
    6c66:	bf 01 00 00 00       	mov    $0x1,%edi
    6c6b:	48 8b 08             	mov    (%rax),%rcx
    6c6e:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    6c78:	48 f7 e9             	imul   %rcx
    6c7b:	48 c1 f9 3f          	sar    $0x3f,%rcx
    6c7f:	31 c0                	xor    %eax,%eax
    6c81:	48 d1 fa             	sar    %rdx
    6c84:	48 29 ca             	sub    %rcx,%rdx
    6c87:	e8 94 d8 ff ff       	call   4520 <__printf_chk@plt>
    6c8c:	bf 0a 00 00 00       	mov    $0xa,%edi
    6c91:	e8 9a d8 ff ff       	call   4530 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    6c96:	4c 89 e8             	mov    %r13,%rax
    6c99:	48 c1 e8 03          	shr    $0x3,%rax
    6c9d:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    6ca4:	84 c0                	test   %al,%al
    6ca6:	74 08                	je     6cb0 <main+0x2220>
    6ca8:	3c 03                	cmp    $0x3,%al
    6caa:	0f 8e 42 0c 00 00    	jle    78f2 <main+0x2e62>
    6cb0:	8b 45 08             	mov    0x8(%rbp),%eax
    6cb3:	85 c0                	test   %eax,%eax
    6cb5:	0f 8e 2a 01 00 00    	jle    6de5 <main+0x2355>
      total += thread_data[x].tasks[n].n;
    6cbb:	48 89 ea             	mov    %rbp,%rdx
    6cbe:	48 c1 ea 03          	shr    $0x3,%rdx
    6cc2:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    6cc9:	0f 85 1b 0c 00 00    	jne    78ea <main+0x2e5a>
    6ccf:	48 8b 5d 00          	mov    0x0(%rbp),%rbx
    6cd3:	48 63 c8             	movslq %eax,%rcx
    6cd6:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    6cdb:	48 c1 e1 09          	shl    $0x9,%rcx
    6cdf:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6ce4:	48 8d bb 08 01 00 00 	lea    0x108(%rbx),%rdi
    6ceb:	48 01 f9             	add    %rdi,%rcx
    6cee:	66 90                	xchg   %ax,%ax
    6cf0:	48 89 f8             	mov    %rdi,%rax
    6cf3:	48 c1 e8 03          	shr    $0x3,%rax
    6cf7:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6cfe:	0f 85 e1 0b 00 00    	jne    78e5 <main+0x2e55>
      ingests += thread_data[x].tasks[n].ingest_count;
    6d04:	48 8d 47 60          	lea    0x60(%rdi),%rax
      total += thread_data[x].tasks[n].n;
    6d08:	4c 03 3f             	add    (%rdi),%r15
      ingests += thread_data[x].tasks[n].ingest_count;
    6d0b:	48 89 c2             	mov    %rax,%rdx
    6d0e:	48 c1 ea 03          	shr    $0x3,%rdx
    6d12:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    6d19:	0f 85 be 0b 00 00    	jne    78dd <main+0x2e4d>
      sends += thread_data[x].tasks[n].sends;
    6d1f:	48 8d 47 70          	lea    0x70(%rdi),%rax
      ingests += thread_data[x].tasks[n].ingest_count;
    6d23:	4c 03 77 60          	add    0x60(%rdi),%r14
      sends += thread_data[x].tasks[n].sends;
    6d27:	48 89 c2             	mov    %rax,%rdx
    6d2a:	48 c1 ea 03          	shr    $0x3,%rdx
    6d2e:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    6d35:	0f 85 9a 0b 00 00    	jne    78d5 <main+0x2e45>
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    6d3b:	48 8d 47 68          	lea    0x68(%rdi),%rax
      sends += thread_data[x].tasks[n].sends;
    6d3f:	4c 03 57 70          	add    0x70(%rdi),%r10
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    6d43:	48 89 c2             	mov    %rax,%rdx
    6d46:	48 c1 ea 03          	shr    $0x3,%rdx
    6d4a:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    6d51:	0f 85 76 0b 00 00    	jne    78cd <main+0x2e3d>
    6d57:	48 8b 47 68          	mov    0x68(%rdi),%rax
    6d5b:	48 8d 50 10          	lea    0x10(%rax),%rdx
    6d5f:	48 89 d6             	mov    %rdx,%rsi
    6d62:	48 c1 ee 03          	shr    $0x3,%rsi
    6d66:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    6d6d:	0f 85 52 0b 00 00    	jne    78c5 <main+0x2e35>
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    6d73:	48 8d 50 18          	lea    0x18(%rax),%rdx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    6d77:	4c 03 58 10          	add    0x10(%rax),%r11
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    6d7b:	48 89 d6             	mov    %rdx,%rsi
    6d7e:	48 c1 ee 03          	shr    $0x3,%rsi
    6d82:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    6d89:	0f 85 2e 0b 00 00    	jne    78bd <main+0x2e2d>
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    6d8f:	48 8d 50 38          	lea    0x38(%rax),%rdx
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    6d93:	4c 03 60 18          	add    0x18(%rax),%r12
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    6d97:	48 89 d6             	mov    %rdx,%rsi
    6d9a:	48 c1 ee 03          	shr    $0x3,%rsi
    6d9e:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    6da5:	0f 85 cf 0a 00 00    	jne    787a <main+0x2dea>
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    6dab:	48 8d 50 40          	lea    0x40(%rax),%rdx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    6daf:	4c 03 58 38          	add    0x38(%rax),%r11
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    6db3:	48 89 d6             	mov    %rdx,%rsi
    6db6:	48 c1 ee 03          	shr    $0x3,%rsi
    6dba:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    6dc1:	0f 85 ab 0a 00 00    	jne    7872 <main+0x2de2>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    6dc7:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    6dce:	4c 03 60 40          	add    0x40(%rax),%r12
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    6dd2:	48 39 f9             	cmp    %rdi,%rcx
    6dd5:	0f 85 15 ff ff ff    	jne    6cf0 <main+0x2260>
    6ddb:	4c 89 5c 24 18       	mov    %r11,0x18(%rsp)
    6de0:	4c 89 54 24 20       	mov    %r10,0x20(%rsp)
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    6de5:	48 8d 7d 50          	lea    0x50(%rbp),%rdi
    6de9:	48 89 f8             	mov    %rdi,%rax
    6dec:	48 c1 e8 03          	shr    $0x3,%rax
    6df0:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6df7:	0f 85 70 0a 00 00    	jne    786d <main+0x2ddd>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    6dfd:	48 8d 4d 68          	lea    0x68(%rbp),%rcx
    6e01:	48 89 cb             	mov    %rcx,%rbx
    6e04:	48 c1 eb 03          	shr    $0x3,%rbx
    6e08:	80 bb 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rbx)
    6e0f:	0f 85 50 0a 00 00    	jne    7865 <main+0x2dd5>
    6e15:	48 8d 75 58          	lea    0x58(%rbp),%rsi
    6e19:	45 31 ed             	xor    %r13d,%r13d
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    6e1c:	48 89 f0             	mov    %rsi,%rax
    6e1f:	48 c1 e8 03          	shr    $0x3,%rax
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    6e23:	48 83 7d 68 00       	cmpq   $0x0,0x68(%rbp)
    6e28:	0f 8e 15 01 00 00    	jle    6f43 <main+0x24b3>
    6e2e:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    6e33:	48 89 74 24 10       	mov    %rsi,0x10(%rsp)
    6e38:	4c 89 24 24          	mov    %r12,(%rsp)
    6e3c:	49 89 c4             	mov    %rax,%r12
    6e3f:	90                   	nop
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    6e40:	41 80 bc 24 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r12)
    6e49:	0f 85 0c 0a 00 00    	jne    785b <main+0x2dcb>
    6e4f:	48 8b 55 58          	mov    0x58(%rbp),%rdx
    6e53:	4b 8d 44 ad 00       	lea    0x0(%r13,%r13,4),%rax
    6e58:	48 8d 3c c2          	lea    (%rdx,%rax,8),%rdi
    6e5c:	48 89 f8             	mov    %rdi,%rax
    6e5f:	48 c1 e8 03          	shr    $0x3,%rax
    6e63:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6e6a:	0f 85 e6 09 00 00    	jne    7856 <main+0x2dc6>
    6e70:	48 8d 47 08          	lea    0x8(%rdi),%rax
    6e74:	48 8b 0f             	mov    (%rdi),%rcx
    6e77:	48 89 c2             	mov    %rax,%rdx
    6e7a:	48 c1 ea 03          	shr    $0x3,%rdx
    6e7e:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    6e85:	0f 85 c3 09 00 00    	jne    784e <main+0x2dbe>
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
    6e8b:	48 8d 47 10          	lea    0x10(%rdi),%rax
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    6e8f:	48 8b 57 08          	mov    0x8(%rdi),%rdx
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
    6e93:	48 89 c6             	mov    %rax,%rsi
    6e96:	48 c1 ee 03          	shr    $0x3,%rsi
    6e9a:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    6ea1:	0f 85 9f 09 00 00    	jne    7846 <main+0x2db6>
    6ea7:	48 8d 47 18          	lea    0x18(%rdi),%rax
    6eab:	4c 8b 47 10          	mov    0x10(%rdi),%r8
    6eaf:	48 89 c6             	mov    %rax,%rsi
    6eb2:	48 c1 ee 03          	shr    $0x3,%rsi
    6eb6:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    6ebd:	0f 85 7b 09 00 00    	jne    783e <main+0x2dae>
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    6ec3:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    6ecd:	49 29 c8             	sub    %rcx,%r8
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    6ed0:	48 8b 4f 18          	mov    0x18(%rdi),%rcx
    6ed4:	48 29 d1             	sub    %rdx,%rcx
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    6ed7:	48 f7 e1             	mul    %rcx
    6eda:	48 c1 ea 12          	shr    $0x12,%rdx
    6ede:	49 89 d1             	mov    %rdx,%r9
    6ee1:	48 8d 57 20          	lea    0x20(%rdi),%rdx
    6ee5:	48 89 d0             	mov    %rdx,%rax
    6ee8:	48 c1 e8 03          	shr    $0x3,%rax
    6eec:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    6ef3:	84 c0                	test   %al,%al
    6ef5:	74 08                	je     6eff <main+0x246f>
    6ef7:	3c 03                	cmp    $0x3,%al
    6ef9:	0f 8e b0 07 00 00    	jle    76af <main+0x2c1f>
    6eff:	48 83 ec 08          	sub    $0x8,%rsp
    6f03:	8b 47 20             	mov    0x20(%rdi),%eax
    6f06:	ba 02 00 00 00       	mov    $0x2,%edx
    6f0b:	bf 01 00 00 00       	mov    $0x1,%edi
    6f10:	51                   	push   %rcx
    6f11:	48 8d 35 88 aa 00 00 	lea    0xaa88(%rip),%rsi        # 119a0 <_IO_stdin_used+0x19a0>
    6f18:	89 c1                	mov    %eax,%ecx
    6f1a:	31 c0                	xor    %eax,%eax
    6f1c:	e8 ff d5 ff ff       	call   4520 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    6f21:	80 bb 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rbx)
    6f28:	5f                   	pop    %rdi
    6f29:	41 58                	pop    %r8
    6f2b:	0f 85 74 07 00 00    	jne    76a5 <main+0x2c15>
    6f31:	49 83 c5 01          	add    $0x1,%r13
    6f35:	4c 39 6d 68          	cmp    %r13,0x68(%rbp)
    6f39:	0f 8f 01 ff ff ff    	jg     6e40 <main+0x23b0>
    6f3f:	4c 8b 24 24          	mov    (%rsp),%r12
    for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    6f43:	48 8d bd 84 00 00 00 	lea    0x84(%rbp),%rdi
    6f4a:	48 89 f8             	mov    %rdi,%rax
    6f4d:	48 c1 e8 03          	shr    $0x3,%rax
    6f51:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    6f58:	48 89 f8             	mov    %rdi,%rax
    6f5b:	83 e0 07             	and    $0x7,%eax
    6f5e:	83 c0 03             	add    $0x3,%eax
    6f61:	38 d0                	cmp    %dl,%al
    6f63:	7c 08                	jl     6f6d <main+0x24dd>
    6f65:	84 d2                	test   %dl,%dl
    6f67:	0f 85 33 07 00 00    	jne    76a0 <main+0x2c10>
    6f6d:	8b 85 84 00 00 00    	mov    0x84(%rbp),%eax
    6f73:	85 c0                	test   %eax,%eax
    6f75:	0f 8e ae 02 00 00    	jle    7229 <main+0x2799>
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    6f7b:	48 8d 5d 18          	lea    0x18(%rbp),%rbx
    6f7f:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    6f84:	48 c1 eb 03          	shr    $0x3,%rbx
    6f88:	80 bb 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rbx)
    6f8f:	0f 85 01 07 00 00    	jne    7696 <main+0x2c06>
    6f95:	4c 89 7c 24 40       	mov    %r15,0x40(%rsp)
    6f9a:	31 db                	xor    %ebx,%ebx
    6f9c:	4c 8b 4d 18          	mov    0x18(%rbp),%r9
    6fa0:	4c 89 74 24 48       	mov    %r14,0x48(%rsp)
    6fa5:	4c 89 64 24 38       	mov    %r12,0x38(%rsp)
    6faa:	49 89 dc             	mov    %rbx,%r12
    6fad:	0f 1f 00             	nopl   (%rax)
    6fb0:	4e 8d 3c e5 00 00 00 00 	lea    0x0(,%r12,8),%r15
    6fb8:	44 89 e3             	mov    %r12d,%ebx
    6fbb:	4b 8d 3c 39          	lea    (%r9,%r15,1),%rdi
    6fbf:	48 89 fa             	mov    %rdi,%rdx
    6fc2:	48 c1 ea 03          	shr    $0x3,%rdx
    6fc6:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    6fcd:	0f 85 be 06 00 00    	jne    7691 <main+0x2c01>
    6fd3:	48 8b 3f             	mov    (%rdi),%rdi
    6fd6:	48 89 fa             	mov    %rdi,%rdx
    6fd9:	48 c1 ea 03          	shr    $0x3,%rdx
    6fdd:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    6fe4:	84 d2                	test   %dl,%dl
    6fe6:	74 09                	je     6ff1 <main+0x2561>
    6fe8:	80 fa 03             	cmp    $0x3,%dl
    6feb:	0f 8e 9b 06 00 00    	jle    768c <main+0x2bfc>
    6ff1:	8b 0f                	mov    (%rdi),%ecx
    6ff3:	85 c9                	test   %ecx,%ecx
    6ff5:	0f 8e 12 02 00 00    	jle    720d <main+0x277d>
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    6ffb:	48 8d 47 08          	lea    0x8(%rdi),%rax
    6fff:	48 89 c2             	mov    %rax,%rdx
    7002:	48 c1 ea 03          	shr    $0x3,%rdx
    7006:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    700d:	0f 85 71 06 00 00    	jne    7684 <main+0x2bf4>
    7013:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    7018:	4c 8b 47 08          	mov    0x8(%rdi),%r8
    701c:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
    7021:	31 f6                	xor    %esi,%esi
    7023:	49 c1 ed 03          	shr    $0x3,%r13
    7027:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    7030:	49 89 f4             	mov    %rsi,%r12
    7033:	49 c1 e4 08          	shl    $0x8,%r12
    7037:	4b 8d 04 20          	lea    (%r8,%r12,1),%rax
    703b:	48 8d b8 94 00 00 00 	lea    0x94(%rax),%rdi
    7042:	48 89 fa             	mov    %rdi,%rdx
    7045:	48 c1 ea 03          	shr    $0x3,%rdx
    7049:	44 0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%r10d
    7051:	48 89 fa             	mov    %rdi,%rdx
    7054:	83 e2 07             	and    $0x7,%edx
    7057:	83 c2 03             	add    $0x3,%edx
    705a:	44 38 d2             	cmp    %r10b,%dl
    705d:	7c 09                	jl     7068 <main+0x25d8>
    705f:	45 84 d2             	test   %r10b,%r10b
    7062:	0f 85 cf 03 00 00    	jne    7437 <main+0x29a7>
    7068:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    706e:	45 31 f6             	xor    %r14d,%r14d
    7071:	85 d2                	test   %edx,%edx
    7073:	0f 8e 7d 01 00 00    	jle    71f6 <main+0x2766>
    7079:	48 89 34 24          	mov    %rsi,(%rsp)
    707d:	0f 1f 00             	nopl   (%rax)
	  struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    7080:	48 8d b8 88 00 00 00 	lea    0x88(%rax),%rdi
    7087:	48 89 fa             	mov    %rdi,%rdx
    708a:	48 c1 ea 03          	shr    $0x3,%rdx
    708e:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    7095:	0f 85 90 03 00 00    	jne    742b <main+0x299b>
    709b:	4c 89 f7             	mov    %r14,%rdi
    709e:	48 c1 e7 05          	shl    $0x5,%rdi
    70a2:	48 03 b8 88 00 00 00 	add    0x88(%rax),%rdi
    70a9:	48 8d 47 10          	lea    0x10(%rdi),%rax
    70ad:	48 89 c2             	mov    %rax,%rdx
    70b0:	48 c1 ea 03          	shr    $0x3,%rdx
    70b4:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    70bb:	0f 85 62 03 00 00    	jne    7423 <main+0x2993>
    70c1:	48 8d 47 18          	lea    0x18(%rdi),%rax
    70c5:	4c 8b 47 10          	mov    0x10(%rdi),%r8
    70c9:	48 89 c2             	mov    %rax,%rdx
    70cc:	48 c1 ea 03          	shr    $0x3,%rdx
    70d0:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    70d7:	0f 85 3e 03 00 00    	jne    741b <main+0x298b>
	  struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
    70dd:	48 89 f8             	mov    %rdi,%rax
	  struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    70e0:	48 8b 4f 18          	mov    0x18(%rdi),%rcx
	  struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
    70e4:	48 c1 e8 03          	shr    $0x3,%rax
    70e8:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    70ef:	0f 85 21 03 00 00    	jne    7416 <main+0x2986>
    70f5:	48 8d 47 08          	lea    0x8(%rdi),%rax
    70f9:	48 8b 37             	mov    (%rdi),%rsi
    70fc:	48 89 c2             	mov    %rax,%rdx
    70ff:	48 c1 ea 03          	shr    $0x3,%rdx
    7103:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    710a:	0f 85 fe 02 00 00    	jne    740e <main+0x297e>
	  const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    7110:	48 2b 4f 08          	sub    0x8(%rdi),%rcx
    7114:	48 83 ec 08          	sub    $0x8,%rsp
    7118:	49 29 f0             	sub    %rsi,%r8
    711b:	bf 01 00 00 00       	mov    $0x1,%edi
	  printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    7120:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
    712a:	51                   	push   %rcx
    712b:	48 8d 35 ee a8 00 00 	lea    0xa8ee(%rip),%rsi        # 11a20 <_IO_stdin_used+0x1a20>
    7132:	48 f7 e1             	mul    %rcx
    7135:	89 d9                	mov    %ebx,%ecx
    7137:	31 c0                	xor    %eax,%eax
    7139:	48 c1 ea 12          	shr    $0x12,%rdx
    713d:	49 89 d1             	mov    %rdx,%r9
    7140:	ba 02 00 00 00       	mov    $0x2,%edx
    7145:	e8 d6 d3 ff ff       	call   4520 <__printf_chk@plt>
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    714a:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    7152:	59                   	pop    %rcx
    7153:	5e                   	pop    %rsi
    7154:	0f 85 aa 02 00 00    	jne    7404 <main+0x2974>
    715a:	4c 8b 4d 18          	mov    0x18(%rbp),%r9
    715e:	4b 8d 3c 39          	lea    (%r9,%r15,1),%rdi
    7162:	48 89 f8             	mov    %rdi,%rax
    7165:	48 c1 e8 03          	shr    $0x3,%rax
    7169:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    7170:	0f 85 89 02 00 00    	jne    73ff <main+0x296f>
    7176:	48 8b 3f             	mov    (%rdi),%rdi
    7179:	48 8d 47 08          	lea    0x8(%rdi),%rax
    717d:	48 89 c2             	mov    %rax,%rdx
    7180:	48 c1 ea 03          	shr    $0x3,%rdx
    7184:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    718b:	0f 85 66 02 00 00    	jne    73f7 <main+0x2967>
    7191:	4c 8b 47 08          	mov    0x8(%rdi),%r8
    7195:	4b 8d 04 20          	lea    (%r8,%r12,1),%rax
    7199:	48 8d 88 94 00 00 00 	lea    0x94(%rax),%rcx
    71a0:	48 89 ca             	mov    %rcx,%rdx
    71a3:	48 c1 ea 03          	shr    $0x3,%rdx
    71a7:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    71ae:	48 89 ca             	mov    %rcx,%rdx
    71b1:	83 e2 07             	and    $0x7,%edx
    71b4:	83 c2 03             	add    $0x3,%edx
    71b7:	40 38 f2             	cmp    %sil,%dl
    71ba:	7c 09                	jl     71c5 <main+0x2735>
    71bc:	40 84 f6             	test   %sil,%sil
    71bf:	0f 85 2a 02 00 00    	jne    73ef <main+0x295f>
    71c5:	49 83 c6 01          	add    $0x1,%r14
    71c9:	44 39 b0 94 00 00 00 	cmp    %r14d,0x94(%rax)
    71d0:	0f 8f aa fe ff ff    	jg     7080 <main+0x25f0>
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    71d6:	48 89 f8             	mov    %rdi,%rax
    71d9:	48 8b 34 24          	mov    (%rsp),%rsi
    71dd:	48 c1 e8 03          	shr    $0x3,%rax
    71e1:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    71e8:	84 c0                	test   %al,%al
    71ea:	74 08                	je     71f4 <main+0x2764>
    71ec:	3c 03                	cmp    $0x3,%al
    71ee:	0f 8e e2 02 00 00    	jle    74d6 <main+0x2a46>
    71f4:	8b 0f                	mov    (%rdi),%ecx
    71f6:	48 83 c6 01          	add    $0x1,%rsi
    71fa:	39 f1                	cmp    %esi,%ecx
    71fc:	0f 8f 2e fe ff ff    	jg     7030 <main+0x25a0>
    for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    7202:	4c 8b 64 24 08       	mov    0x8(%rsp),%r12
    7207:	8b 85 84 00 00 00    	mov    0x84(%rbp),%eax
    720d:	49 83 c4 01          	add    $0x1,%r12
    7211:	44 39 e0             	cmp    %r12d,%eax
    7214:	0f 8f 96 fd ff ff    	jg     6fb0 <main+0x2520>
    721a:	4c 8b 64 24 38       	mov    0x38(%rsp),%r12
    721f:	4c 8b 7c 24 40       	mov    0x40(%rsp),%r15
    7224:	4c 8b 74 24 48       	mov    0x48(%rsp),%r14
  for (int x = 0 ; x < thread_count ; x++) {
    7229:	8b 44 24 28          	mov    0x28(%rsp),%eax
    722d:	48 81 c5 c0 00 00 00 	add    $0xc0,%rbp
    7234:	48 83 84 24 80 00 00 00 18 	addq   $0x18,0x80(%rsp)
    723d:	85 c0                	test   %eax,%eax
    723f:	75 0d                	jne    724e <main+0x27be>
    7241:	c7 44 24 28 01 00 00 00 	movl   $0x1,0x28(%rsp)
    7249:	e9 87 f8 ff ff       	jmp    6ad5 <main+0x2045>
    724e:	4c 89 fa             	mov    %r15,%rdx
    7251:	48 8d 35 48 a8 00 00 	lea    0xa848(%rip),%rsi        # 11aa0 <_IO_stdin_used+0x1aa0>
    7258:	31 c0                	xor    %eax,%eax
    725a:	4c 89 34 24          	mov    %r14,(%rsp)
    725e:	bf 01 00 00 00       	mov    $0x1,%edi
    7263:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
    7268:	e8 b3 d2 ff ff       	call   4520 <__printf_chk@plt>
    726d:	bf 0a 00 00 00       	mov    $0xa,%edi
    7272:	e8 b9 d2 ff ff       	call   4530 <putchar@plt>
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
    7277:	4c 8b 04 24          	mov    (%rsp),%r8
    727b:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    7280:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    7288:	48 8d 78 08          	lea    0x8(%rax),%rdi
    728c:	48 89 f8             	mov    %rdi,%rax
    728f:	48 c1 e8 03          	shr    $0x3,%rax
    7293:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    729a:	0f 85 7f 03 00 00    	jne    761f <main+0x2b8f>
    72a0:	48 8d 35 39 a8 00 00 	lea    0xa839(%rip),%rsi        # 11ae0 <_IO_stdin_used+0x1ae0>
    72a7:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    72af:	bf 01 00 00 00       	mov    $0x1,%edi
    72b4:	4c 89 14 24          	mov    %r10,(%rsp)
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    72b8:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    72c2:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    72c7:	48 8b 50 08          	mov    0x8(%rax),%rdx
    72cb:	31 c0                	xor    %eax,%eax
    72cd:	e8 4e d2 ff ff       	call   4520 <__printf_chk@plt>
    72d2:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    72d7:	bf 01 00 00 00       	mov    $0x1,%edi
    72dc:	48 8d 35 5d a8 00 00 	lea    0xa85d(%rip),%rsi        # 11b40 <_IO_stdin_used+0x1b40>
    72e3:	4c 89 c0             	mov    %r8,%rax
    72e6:	49 c1 f8 3f          	sar    $0x3f,%r8
    72ea:	48 f7 eb             	imul   %rbx
    72ed:	31 c0                	xor    %eax,%eax
    72ef:	48 d1 fa             	sar    %rdx
    72f2:	4c 29 c2             	sub    %r8,%rdx
    72f5:	e8 26 d2 ff ff       	call   4520 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    72fa:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    72ff:	bf 01 00 00 00       	mov    $0x1,%edi
    7304:	48 8d 35 95 a8 00 00 	lea    0xa895(%rip),%rsi        # 11ba0 <_IO_stdin_used+0x1ba0>
    730b:	48 f7 eb             	imul   %rbx
    730e:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    7313:	48 c1 f8 3f          	sar    $0x3f,%rax
    7317:	48 d1 fa             	sar    %rdx
    731a:	48 29 c2             	sub    %rax,%rdx
    731d:	31 c0                	xor    %eax,%eax
    731f:	e8 fc d1 ff ff       	call   4520 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    7324:	4c 89 f8             	mov    %r15,%rax
    7327:	49 c1 ff 3f          	sar    $0x3f,%r15
    732b:	48 8d 35 ce a8 00 00 	lea    0xa8ce(%rip),%rsi        # 11c00 <_IO_stdin_used+0x1c00>
    7332:	48 f7 eb             	imul   %rbx
    7335:	bf 01 00 00 00       	mov    $0x1,%edi
    733a:	31 c0                	xor    %eax,%eax
    733c:	48 d1 fa             	sar    %rdx
    733f:	4c 29 fa             	sub    %r15,%rdx
    7342:	e8 d9 d1 ff ff       	call   4520 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    7347:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    734c:	bf 01 00 00 00       	mov    $0x1,%edi
    7351:	48 8d 35 e8 a8 00 00 	lea    0xa8e8(%rip),%rsi        # 11c40 <_IO_stdin_used+0x1c40>
    7358:	48 f7 eb             	imul   %rbx
    735b:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7360:	48 c1 f8 3f          	sar    $0x3f,%rax
    7364:	48 d1 fa             	sar    %rdx
    7367:	48 29 c2             	sub    %rax,%rdx
    736a:	31 c0                	xor    %eax,%eax
    736c:	e8 af d1 ff ff       	call   4520 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    7371:	4c 8b 14 24          	mov    (%rsp),%r10
    7375:	bf 01 00 00 00       	mov    $0x1,%edi
    737a:	48 8d 35 ff a8 00 00 	lea    0xa8ff(%rip),%rsi        # 11c80 <_IO_stdin_used+0x1c80>
    7381:	4c 89 d0             	mov    %r10,%rax
    7384:	48 f7 eb             	imul   %rbx
    7387:	4c 89 d0             	mov    %r10,%rax
    738a:	48 c1 f8 3f          	sar    $0x3f,%rax
    738e:	48 d1 fa             	sar    %rdx
    7391:	48 29 c2             	sub    %rax,%rdx
    7394:	31 c0                	xor    %eax,%eax
    7396:	e8 85 d1 ff ff       	call   4520 <__printf_chk@plt>
int main() {
    739b:	48 8b 9c 24 90 00 00 00 	mov    0x90(%rsp),%rbx
    73a3:	48 39 9c 24 b0 00 00 00 	cmp    %rbx,0xb0(%rsp)
    73ab:	0f 85 3f 02 00 00    	jne    75f0 <main+0x2b60>
    73b1:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    73b9:	48 c7 80 00 80 ff 7f 00 00 00 00 	movq   $0x0,0x7fff8000(%rax)
}
    73c4:	48 8b 84 24 18 01 00 00 	mov    0x118(%rsp),%rax
    73cc:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    73d5:	0f 85 79 02 00 00    	jne    7654 <main+0x2bc4>
    73db:	48 81 c4 28 01 00 00 	add    $0x128,%rsp
    73e2:	31 c0                	xor    %eax,%eax
    73e4:	5b                   	pop    %rbx
    73e5:	5d                   	pop    %rbp
    73e6:	41 5c                	pop    %r12
    73e8:	41 5d                	pop    %r13
    73ea:	41 5e                	pop    %r14
    73ec:	41 5f                	pop    %r15
    73ee:	c3                   	ret
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    73ef:	48 89 cf             	mov    %rcx,%rdi
    73f2:	e8 59 d1 ff ff       	call   4550 <__asan_report_load4@plt>
    73f7:	48 89 c7             	mov    %rax,%rdi
    73fa:	e8 e1 d0 ff ff       	call   44e0 <__asan_report_load8@plt>
    73ff:	e8 dc d0 ff ff       	call   44e0 <__asan_report_load8@plt>
    7404:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    7409:	e8 d2 d0 ff ff       	call   44e0 <__asan_report_load8@plt>
	  struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
    740e:	48 89 c7             	mov    %rax,%rdi
    7411:	e8 ca d0 ff ff       	call   44e0 <__asan_report_load8@plt>
    7416:	e8 c5 d0 ff ff       	call   44e0 <__asan_report_load8@plt>
	  struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    741b:	48 89 c7             	mov    %rax,%rdi
    741e:	e8 bd d0 ff ff       	call   44e0 <__asan_report_load8@plt>
    7423:	48 89 c7             	mov    %rax,%rdi
    7426:	e8 b5 d0 ff ff       	call   44e0 <__asan_report_load8@plt>
    742b:	e8 b0 d0 ff ff       	call   44e0 <__asan_report_load8@plt>
    long v = 0;
    7430:	31 d2                	xor    %edx,%edx
    7432:	e9 64 f7 ff ff       	jmp    6b9b <main+0x210b>
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    7437:	e8 14 d1 ff ff       	call   4550 <__asan_report_load4@plt>
              mailboxes[b].lower = &data[0];
    743c:	4c 89 ff             	mov    %r15,%rdi
    743f:	e8 8c d2 ff ff       	call   46d0 <__asan_report_store8@plt>
              mailboxes[b].higher = &data[1];
    7444:	48 89 f7             	mov    %rsi,%rdi
    7447:	e8 84 d2 ff ff       	call   46d0 <__asan_report_store8@plt>
              mailboxes[b].kind = MAILBOX_FRIEND;
    744c:	4c 89 c7             	mov    %r8,%rdi
    744f:	e8 6c d2 ff ff       	call   46c0 <__asan_report_store4@plt>
              data[0].messages = messages;
    7454:	e8 77 d2 ff ff       	call   46d0 <__asan_report_store8@plt>
              data[1].messages = messages2;
    7459:	48 89 c7             	mov    %rax,%rdi
    745c:	e8 6f d2 ff ff       	call   46d0 <__asan_report_store8@plt>
              data[0].messages_limit = messages_limit;
    7461:	48 89 c7             	mov    %rax,%rdi
    7464:	e8 67 d2 ff ff       	call   46d0 <__asan_report_store8@plt>
              data[0].messages_count = 0;
    7469:	48 89 c7             	mov    %rax,%rdi
    746c:	e8 5f d2 ff ff       	call   46d0 <__asan_report_store8@plt>
              data[1].messages_count = 0;
    7471:	48 89 c7             	mov    %rax,%rdi
    7474:	e8 57 d2 ff ff       	call   46d0 <__asan_report_store8@plt>
              data[1].messages_limit = messages_limit;
    7479:	48 89 c7             	mov    %rax,%rdi
    747c:	e8 4f d2 ff ff       	call   46d0 <__asan_report_store8@plt>
            mailboxes[b].lower = &data[0];
    7481:	48 89 df             	mov    %rbx,%rdi
    7484:	e8 47 d2 ff ff       	call   46d0 <__asan_report_store8@plt>
            mailboxes[b].higher = &data[1];
    7489:	48 89 cf             	mov    %rcx,%rdi
    748c:	e8 3f d2 ff ff       	call   46d0 <__asan_report_store8@plt>
            mailboxes[b].kind = MAILBOX_FOREIGN;
    7491:	48 89 f7             	mov    %rsi,%rdi
    7494:	e8 27 d2 ff ff       	call   46c0 <__asan_report_store4@plt>
            data[0].available = 0;
    7499:	48 89 f7             	mov    %rsi,%rdi
    749c:	e8 1f d2 ff ff       	call   46c0 <__asan_report_store4@plt>
            data[0].messages = messages;
    74a1:	e8 2a d2 ff ff       	call   46d0 <__asan_report_store8@plt>
            data[1].messages = messages2;
    74a6:	48 89 c7             	mov    %rax,%rdi
    74a9:	e8 22 d2 ff ff       	call   46d0 <__asan_report_store8@plt>
            data[1].available = 0;
    74ae:	48 89 cf             	mov    %rcx,%rdi
    74b1:	e8 0a d2 ff ff       	call   46c0 <__asan_report_store4@plt>
            data[0].messages_limit = messages_limit;
    74b6:	48 89 c7             	mov    %rax,%rdi
    74b9:	e8 12 d2 ff ff       	call   46d0 <__asan_report_store8@plt>
            data[0].messages_count = 0;
    74be:	48 89 c7             	mov    %rax,%rdi
    74c1:	e8 0a d2 ff ff       	call   46d0 <__asan_report_store8@plt>
            data[1].messages_count = 0;
    74c6:	48 89 c7             	mov    %rax,%rdi
    74c9:	e8 02 d2 ff ff       	call   46d0 <__asan_report_store8@plt>
            data[1].messages_limit = messages_limit;
    74ce:	48 89 c7             	mov    %rax,%rdi
    74d1:	e8 fa d1 ff ff       	call   46d0 <__asan_report_store8@plt>
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    74d6:	e8 75 d0 ff ff       	call   4550 <__asan_report_load4@plt>
    thread_data[x].thread_count = 2;
    74db:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    74e0:	e8 db d1 ff ff       	call   46c0 <__asan_report_store4@plt>
        thread_data[x].tasks[barrier_count].available = 1; 
    74e5:	e8 d6 d1 ff ff       	call   46c0 <__asan_report_store4@plt>
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    74ea:	e8 e1 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    74ef:	e8 dc d1 ff ff       	call   46d0 <__asan_report_store8@plt>
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
    74f4:	e8 d7 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    74f9:	e8 d2 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    74fe:	48 89 c7             	mov    %rax,%rdi
    7501:	e8 ca d1 ff ff       	call   46d0 <__asan_report_store8@plt>
        thread_data[x].buffers_count = buffers_per_thread;
    7506:	e8 b5 d1 ff ff       	call   46c0 <__asan_report_store4@plt>
               thread_data[x].tasks[y].run = barriered_work; 
    750b:	e8 c0 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
          thread_data[x].tasks[y].task_index = y;
    7510:	e8 ab d1 ff ff       	call   46c0 <__asan_report_store4@plt>
    my_thread_data[n] = &thread_data[n]; 
    7515:	48 89 c7             	mov    %rax,%rdi
    7518:	e8 b3 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
    751d:	48 89 c7             	mov    %rax,%rdi
    7520:	e8 ab d1 ff ff       	call   46d0 <__asan_report_store8@plt>
    7525:	48 89 c7             	mov    %rax,%rdi
    7528:	e8 a3 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
    752d:	e8 9e d1 ff ff       	call   46d0 <__asan_report_store8@plt>
    thread_data[x].threads = my_thread_data;
    7532:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    7537:	e8 94 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    753c:	48 89 c7             	mov    %rax,%rdi
    753f:	e8 8c d1 ff ff       	call   46d0 <__asan_report_store8@plt>
    my_thread_data[0] = &thread_data[x]; 
    7544:	e8 87 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
            CPU_SET(j, sendercpu);
    7549:	4c 89 ff             	mov    %r15,%rdi
    754c:	e8 8f cf ff ff       	call   44e0 <__asan_report_load8@plt>
          thread_data[x].tasks[y].sending = 1;
    7551:	e8 6a d1 ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].message = messaged;
    7556:	e8 75 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    755b:	e8 60 d1 ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    7560:	48 89 df             	mov    %rbx,%rdi
    7563:	e8 58 d1 ff ff       	call   46c0 <__asan_report_store4@plt>
    7568:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    756d:	e8 6e cf ff ff       	call   44e0 <__asan_report_load8@plt>
          messaged->thread_index = thread_data[x].thread_index;
    7572:	e8 59 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
    7577:	48 89 df             	mov    %rbx,%rdi
    757a:	e8 d1 cf ff ff       	call   4550 <__asan_report_load4@plt>
          messaged->task_index = y;
    757f:	e8 4c d1 ff ff       	call   46d0 <__asan_report_store8@plt>
          thread_data[x].tasks[y].worker_count = thread_count;
    7584:	e8 37 d1 ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].task_count = total_barrier_count;
    7589:	e8 32 d1 ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
    758e:	e8 2d d1 ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].all_thread_count = thread_count;
    7593:	e8 28 d1 ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].total_thread_count = thread_count;
    7598:	e8 23 d1 ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].thread_count = 2;
    759d:	e8 1e d1 ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].arrived = 0;
    75a2:	e8 19 d1 ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].available = 1;
    75a7:	e8 14 d1 ff ff       	call   46c0 <__asan_report_store4@plt>
            exit(1);
    75ac:	e8 5f d0 ff ff       	call   4610 <__asan_handle_no_return@plt>
    75b1:	bf 01 00 00 00       	mov    $0x1,%edi
    75b6:	e8 55 cf ff ff       	call   4510 <exit@plt>
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    75bb:	e8 10 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    75c0:	e8 fb d0 ff ff       	call   46c0 <__asan_report_store4@plt>
    75c5:	e8 86 cf ff ff       	call   4550 <__asan_report_load4@plt>
    75ca:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    75cf:	e8 0c cf ff ff       	call   44e0 <__asan_report_load8@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
    75d4:	e8 f7 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    75d9:	e8 f2 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
          thread_data[x].tasks[y].snapshot_count = 99;
    75de:	e8 ed d0 ff ff       	call   46d0 <__asan_report_store8@plt>
  thread_data[timer_threadi].threads = my_thread_data;
    75e3:	48 89 c7             	mov    %rax,%rdi
    75e6:	e8 e5 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
    thread_data[n].tasks[0].scheduled = 1;
    75eb:	e8 f0 ce ff ff       	call   44e0 <__asan_report_load8@plt>
int main() {
    75f0:	48 c7 03 0e 36 e0 45 	movq   $0x45e0360e,(%rbx)
    75f7:	48 89 d8             	mov    %rbx,%rax
    75fa:	48 8b 9c 24 a8 00 00 00 	mov    0xa8(%rsp),%rbx
    7602:	48 be f5 f5 f5 f5 f5 f5 f5 f5 	movabs $0xf5f5f5f5f5f5f5f5,%rsi
    760c:	48 89 b3 00 80 ff 7f 	mov    %rsi,0x7fff8000(%rbx)
    7613:	48 8b 40 38          	mov    0x38(%rax),%rax
    7617:	c6 00 00             	movb   $0x0,(%rax)
    761a:	e9 a5 fd ff ff       	jmp    73c4 <main+0x2934>
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
    761f:	e8 bc ce ff ff       	call   44e0 <__asan_report_load8@plt>
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    7624:	e8 a7 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
    buffers[x].count = buffer_size;
    7629:	4c 89 ef             	mov    %r13,%rdi
    762c:	e8 8f d0 ff ff       	call   46c0 <__asan_report_store4@plt>
int main() {
    7631:	bf 40 00 00 00       	mov    $0x40,%edi
    7636:	e8 75 d1 ff ff       	call   47b0 <__asan_stack_malloc_0@plt>
    763b:	48 85 c0             	test   %rax,%rax
    763e:	48 0f 44 84 24 90 00 00 00 	cmove  0x90(%rsp),%rax
    7647:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
    764f:	e9 79 d4 ff ff       	jmp    4acd <main+0x3d>
}
    7654:	e8 57 d0 ff ff       	call   46b0 <__stack_chk_fail@plt>
      thread_data[x].other = other;
    7659:	e8 62 d0 ff ff       	call   46c0 <__asan_report_store4@plt>
        my_thread_data[0] = &thread_data[other]; 
    765e:	4c 89 e7             	mov    %r12,%rdi
    7661:	e8 6a d0 ff ff       	call   46d0 <__asan_report_store8@plt>
        my_thread_data[1] = &thread_data[x]; 
    7666:	e8 65 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
        thread_data[x].protected_state = &protected_state[k];
    766b:	e8 60 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
        thread_data[x].thread_index = 1;
    7670:	e8 4b d0 ff ff       	call   46c0 <__asan_report_store4@plt>
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    7675:	e8 56 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    767a:	e8 41 d0 ff ff       	call   46c0 <__asan_report_store4@plt>
      buffers[x].buffer[y].available = 0;
    767f:	e8 3c d0 ff ff       	call   46c0 <__asan_report_store4@plt>
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    7684:	48 89 c7             	mov    %rax,%rdi
    7687:	e8 54 ce ff ff       	call   44e0 <__asan_report_load8@plt>
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    768c:	e8 bf ce ff ff       	call   4550 <__asan_report_load4@plt>
    7691:	e8 4a ce ff ff       	call   44e0 <__asan_report_load8@plt>
    7696:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    769b:	e8 40 ce ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    76a0:	e8 ab ce ff ff       	call   4550 <__asan_report_load4@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    76a5:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    76aa:	e8 31 ce ff ff       	call   44e0 <__asan_report_load8@plt>
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    76af:	48 89 d7             	mov    %rdx,%rdi
    76b2:	e8 99 ce ff ff       	call   4550 <__asan_report_load4@plt>
      thread_data[x].task_count = total_barrier_count;
    76b7:	e8 04 d0 ff ff       	call   46c0 <__asan_report_store4@plt>
      thread_data[x].total_thread_count = total_threads;
    76bc:	e8 ff cf ff ff       	call   46c0 <__asan_report_store4@plt>
      thread_data[x].thread_count = 2;
    76c1:	e8 fa cf ff ff       	call   46c0 <__asan_report_store4@plt>
      thread_data[x].all_threads = thread_data;
    76c6:	e8 05 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].threads = my_thread_data;
    76cb:	e8 00 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].real_thread_index = x;
    76d0:	e8 eb cf ff ff       	call   46c0 <__asan_report_store4@plt>
      thread_data[x].cpu_set = sendercpu;
    76d5:	e8 f6 cf ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].kind = KERNEL_THREAD;
    76da:	4c 89 d7             	mov    %r10,%rdi
    76dd:	e8 de cf ff ff       	call   46c0 <__asan_report_store4@plt>
          CPU_SET(curcpu, sendercpu);
    76e2:	e8 f9 cd ff ff       	call   44e0 <__asan_report_load8@plt>
      my_thread_data[n] = &thread_data[n]; 
    76e7:	e8 e4 cf ff ff       	call   46d0 <__asan_report_store8@plt>
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    76ec:	e8 df cf ff ff       	call   46d0 <__asan_report_store8@plt>
    thread_data[x].threads = my_thread_data;
    76f1:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    76f6:	e8 d5 cf ff ff       	call   46d0 <__asan_report_store8@plt>
      my_thread_data[n] = &thread_data[n]; 
    76fb:	48 89 c7             	mov    %rax,%rdi
    76fe:	e8 cd cf ff ff       	call   46d0 <__asan_report_store8@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    7703:	4c 89 e7             	mov    %r12,%rdi
    7706:	e8 d5 cd ff ff       	call   44e0 <__asan_report_load8@plt>
    770b:	e8 d0 cd ff ff       	call   44e0 <__asan_report_load8@plt>
      thread_data[x].running = 1;
    7710:	e8 ab cf ff ff       	call   46c0 <__asan_report_store4@plt>
      thread_data[x].type = WORKER;
    7715:	e8 a6 cf ff ff       	call   46c0 <__asan_report_store4@plt>
    my_thread_data[n] = &thread_data[n]; 
    771a:	48 89 c7             	mov    %rax,%rdi
    771d:	e8 ae cf ff ff       	call   46d0 <__asan_report_store8@plt>
    7722:	48 89 c7             	mov    %rax,%rdi
    7725:	e8 a6 cf ff ff       	call   46d0 <__asan_report_store8@plt>
    772a:	48 89 c7             	mov    %rax,%rdi
    772d:	e8 9e cf ff ff       	call   46d0 <__asan_report_store8@plt>
    7732:	48 89 c7             	mov    %rax,%rdi
    7735:	e8 96 cf ff ff       	call   46d0 <__asan_report_store8@plt>
    773a:	48 89 c7             	mov    %rax,%rdi
    773d:	e8 8e cf ff ff       	call   46d0 <__asan_report_store8@plt>
    7742:	48 89 c7             	mov    %rax,%rdi
    7745:	e8 86 cf ff ff       	call   46d0 <__asan_report_store8@plt>
    774a:	48 89 c7             	mov    %rax,%rdi
    774d:	e8 7e cf ff ff       	call   46d0 <__asan_report_store8@plt>
    7752:	48 89 c7             	mov    %rax,%rdi
    7755:	e8 76 cf ff ff       	call   46d0 <__asan_report_store8@plt>
            thread_data[x].tasks[y].run = barriered_work; 
    775a:	e8 71 cf ff ff       	call   46d0 <__asan_report_store8@plt>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    775f:	e8 5c cf ff ff       	call   46c0 <__asan_report_store4@plt>
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    7764:	e8 57 cf ff ff       	call   46c0 <__asan_report_store4@plt>
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    7769:	e8 52 cf ff ff       	call   46c0 <__asan_report_store4@plt>
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    776e:	e8 4d cf ff ff       	call   46c0 <__asan_report_store4@plt>
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    7773:	e8 48 cf ff ff       	call   46c0 <__asan_report_store4@plt>
        thread_data[x].tasks[barrier_count].arrived = 0; 
    7778:	e8 43 cf ff ff       	call   46c0 <__asan_report_store4@plt>
        thread_data[x].tasks = barriers;
    777d:	4c 89 cf             	mov    %r9,%rdi
    7780:	e8 4b cf ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].task_timestamp_limit = timestamp_limit;
    7785:	e8 46 cf ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].task_timestamp_count = 0;
    778a:	e8 41 cf ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    778f:	e8 3c cf ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].timestamp_limit = timestamp_limit;
    7794:	e8 37 cf ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].timestamp_count = 0;
    7799:	e8 32 cf ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    779e:	e8 2d cf ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    77a3:	e8 28 cf ff ff       	call   46d0 <__asan_report_store8@plt>
  thread_data[timer_threadi].my_thread_count = 2;
    77a8:	e8 13 cf ff ff       	call   46c0 <__asan_report_store4@plt>
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    77ad:	e8 0e cf ff ff       	call   46c0 <__asan_report_store4@plt>
  thread_data[timer_threadi].task_count = total_barrier_count;
    77b2:	e8 09 cf ff ff       	call   46c0 <__asan_report_store4@plt>
  thread_data[timer_threadi].running = 1;
    77b7:	e8 04 cf ff ff       	call   46c0 <__asan_report_store4@plt>
  thread_data[timer_threadi].type = TIMER;
    77bc:	e8 ff ce ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[n].tasks[0].scheduled = 1;
    77c1:	e8 fa ce ff ff       	call   46c0 <__asan_report_store4@plt>
    77c6:	e8 f5 ce ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].task_count = total_barrier_count;
    77cb:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    77d0:	e8 eb ce ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].threads = my_thread_data;
    77d5:	48 89 c7             	mov    %rax,%rdi
    77d8:	e8 f3 ce ff ff       	call   46d0 <__asan_report_store8@plt>
      my_thread_data[n] = &thread_data[n]; 
    77dd:	48 89 c7             	mov    %rax,%rdi
    77e0:	e8 eb ce ff ff       	call   46d0 <__asan_report_store8@plt>
    77e5:	e8 e6 ce ff ff       	call   46d0 <__asan_report_store8@plt>
	  thread_data[x].buffers_count = 1;
    77ea:	e8 d1 ce ff ff       	call   46c0 <__asan_report_store4@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    77ef:	e8 dc ce ff ff       	call   46d0 <__asan_report_store8@plt>
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    77f4:	48 89 c7             	mov    %rax,%rdi
    77f7:	e8 d4 ce ff ff       	call   46d0 <__asan_report_store8@plt>
    thread_data[x].task_count = 0;
    77fc:	e8 bf ce ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].running = 1;
    7801:	e8 ba ce ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].type = EXTERNAL;
    7806:	48 89 ef             	mov    %rbp,%rdi
    7809:	e8 b2 ce ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].thread_index = x;
    780e:	4c 89 ff             	mov    %r15,%rdi
    7811:	e8 aa ce ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].thread_count = thread_count;
    7816:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    781b:	e8 a0 ce ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    7820:	e8 9b ce ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].task_count = 0;
    7825:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    782a:	e8 91 ce ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].running = 1;
    782f:	e8 8c ce ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].type = IO;
    7834:	e8 87 ce ff ff       	call   46c0 <__asan_report_store4@plt>
  thread_data[timer_threadi].thread_index = 0;
    7839:	e8 82 ce ff ff       	call   46c0 <__asan_report_store4@plt>
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
    783e:	48 89 c7             	mov    %rax,%rdi
    7841:	e8 9a cc ff ff       	call   44e0 <__asan_report_load8@plt>
    7846:	48 89 c7             	mov    %rax,%rdi
    7849:	e8 92 cc ff ff       	call   44e0 <__asan_report_load8@plt>
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    784e:	48 89 c7             	mov    %rax,%rdi
    7851:	e8 8a cc ff ff       	call   44e0 <__asan_report_load8@plt>
    7856:	e8 85 cc ff ff       	call   44e0 <__asan_report_load8@plt>
    785b:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    7860:	e8 7b cc ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    7865:	48 89 cf             	mov    %rcx,%rdi
    7868:	e8 73 cc ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    786d:	e8 6e cc ff ff       	call   44e0 <__asan_report_load8@plt>
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    7872:	48 89 d7             	mov    %rdx,%rdi
    7875:	e8 66 cc ff ff       	call   44e0 <__asan_report_load8@plt>
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    787a:	48 89 d7             	mov    %rdx,%rdi
    787d:	e8 5e cc ff ff       	call   44e0 <__asan_report_load8@plt>
    thread_data[n].tasks[0].scheduled = 1;
    7882:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    7887:	e8 54 cc ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    788c:	4c 89 ef             	mov    %r13,%rdi
    788f:	e8 bc cc ff ff       	call   4550 <__asan_report_load4@plt>
      v += thread_data[me].tasks[n].v;
    7894:	e8 47 cc ff ff       	call   44e0 <__asan_report_load8@plt>
    7899:	48 89 ef             	mov    %rbp,%rdi
    789c:	e8 3f cc ff ff       	call   44e0 <__asan_report_load8@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    78a1:	48 8b bc 24 80 00 00 00 	mov    0x80(%rsp),%rdi
    78a9:	e8 32 cc ff ff       	call   44e0 <__asan_report_load8@plt>
      v += thread_data[other].tasks[n].v;
    78ae:	e8 2d cc ff ff       	call   44e0 <__asan_report_load8@plt>
    78b3:	e8 28 cc ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    78b8:	e8 93 cc ff ff       	call   4550 <__asan_report_load4@plt>
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    78bd:	48 89 d7             	mov    %rdx,%rdi
    78c0:	e8 1b cc ff ff       	call   44e0 <__asan_report_load8@plt>
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    78c5:	48 89 d7             	mov    %rdx,%rdi
    78c8:	e8 13 cc ff ff       	call   44e0 <__asan_report_load8@plt>
    78cd:	48 89 c7             	mov    %rax,%rdi
    78d0:	e8 0b cc ff ff       	call   44e0 <__asan_report_load8@plt>
      sends += thread_data[x].tasks[n].sends;
    78d5:	48 89 c7             	mov    %rax,%rdi
    78d8:	e8 03 cc ff ff       	call   44e0 <__asan_report_load8@plt>
      ingests += thread_data[x].tasks[n].ingest_count;
    78dd:	48 89 c7             	mov    %rax,%rdi
    78e0:	e8 fb cb ff ff       	call   44e0 <__asan_report_load8@plt>
      total += thread_data[x].tasks[n].n;
    78e5:	e8 f6 cb ff ff       	call   44e0 <__asan_report_load8@plt>
    78ea:	48 89 ef             	mov    %rbp,%rdi
    78ed:	e8 ee cb ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    78f2:	4c 89 ef             	mov    %r13,%rdi
    78f5:	e8 56 cc ff ff       	call   4550 <__asan_report_load4@plt>
    printf("Total Protected %ld\n", protected_state[me].protected);
    78fa:	48 8b bc 24 80 00 00 00 	mov    0x80(%rsp),%rdi
    7902:	e8 d9 cb ff ff       	call   44e0 <__asan_report_load8@plt>
    pthread_join(thread[x], &result);
    7907:	4c 89 ef             	mov    %r13,%rdi
    790a:	e8 d1 cb ff ff       	call   44e0 <__asan_report_load8@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
    790f:	e8 3c cc ff ff       	call   4550 <__asan_report_load4@plt>
    7914:	4c 89 f7             	mov    %r14,%rdi
    7917:	e8 34 cc ff ff       	call   4550 <__asan_report_load4@plt>
    thread_data[x].thread_index = x;
    791c:	e8 9f cd ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].total_thread_count = total_threads;
    7921:	e8 9a cd ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].thread_count = thread_count;
    7926:	e8 95 cd ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    792b:	e8 a0 cd ff ff       	call   46d0 <__asan_report_store8@plt>
          messaged->message = message;
    7930:	4c 89 df             	mov    %r11,%rdi
    7933:	e8 98 cd ff ff       	call   46d0 <__asan_report_store8@plt>
          thread_data[x].tasks[y].protected = do_protected_write; 
    7938:	e8 93 cd ff ff       	call   46d0 <__asan_report_store8@plt>
    thread_data[x].thread_index = 0;
    793d:	4c 89 ff             	mov    %r15,%rdi
    7940:	e8 7b cd ff ff       	call   46c0 <__asan_report_store4@plt>
    7945:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000007950 <_sub_I_00099_1>:
}
    7950:	f3 0f 1e fa          	endbr64
    7954:	48 83 ec 08          	sub    $0x8,%rsp
    7958:	e8 53 cb ff ff       	call   44b0 <__asan_init@plt>
    795d:	e8 ae ce ff ff       	call   4810 <__asan_version_mismatch_check_v8@plt>
    7962:	be 6b 00 00 00       	mov    $0x6b,%esi
    7967:	48 8d 3d 52 c7 00 00 	lea    0xc752(%rip),%rdi        # 140c0 <unimplemented_content+0x60>
    796e:	48 83 c4 08          	add    $0x8,%rsp
    7972:	e9 e9 cd ff ff       	jmp    4760 <__asan_register_globals@plt>
    7977:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000007980 <_start>:
    7980:	f3 0f 1e fa          	endbr64
    7984:	31 ed                	xor    %ebp,%ebp
    7986:	49 89 d1             	mov    %rdx,%r9
    7989:	5e                   	pop    %rsi
    798a:	48 89 e2             	mov    %rsp,%rdx
    798d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    7991:	50                   	push   %rax
    7992:	54                   	push   %rsp
    7993:	45 31 c0             	xor    %r8d,%r8d
    7996:	31 c9                	xor    %ecx,%ecx
    7998:	48 8d 3d f1 d0 ff ff 	lea    -0x2f0f(%rip),%rdi        # 4a90 <main>
    799f:	ff 15 53 c6 00 00    	call   *0xc653(%rip)        # 13ff8 <__libc_start_main@GLIBC_2.34>
    79a5:	f4                   	hlt
    79a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000079b0 <deregister_tm_clones>:
    79b0:	48 8d 3d c9 e1 00 00 	lea    0xe1c9(%rip),%rdi        # 15b80 <__asan_option_detect_stack_use_after_return@@Base>
    79b7:	48 8d 05 c2 e1 00 00 	lea    0xe1c2(%rip),%rax        # 15b80 <__asan_option_detect_stack_use_after_return@@Base>
    79be:	48 39 f8             	cmp    %rdi,%rax
    79c1:	74 15                	je     79d8 <deregister_tm_clones+0x28>
    79c3:	48 8b 05 16 c6 00 00 	mov    0xc616(%rip),%rax        # 13fe0 <_ITM_deregisterTMCloneTable@Base>
    79ca:	48 85 c0             	test   %rax,%rax
    79cd:	74 09                	je     79d8 <deregister_tm_clones+0x28>
    79cf:	ff e0                	jmp    *%rax
    79d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    79d8:	c3                   	ret
    79d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000079e0 <register_tm_clones>:
    79e0:	48 8d 3d 99 e1 00 00 	lea    0xe199(%rip),%rdi        # 15b80 <__asan_option_detect_stack_use_after_return@@Base>
    79e7:	48 8d 35 92 e1 00 00 	lea    0xe192(%rip),%rsi        # 15b80 <__asan_option_detect_stack_use_after_return@@Base>
    79ee:	48 29 fe             	sub    %rdi,%rsi
    79f1:	48 89 f0             	mov    %rsi,%rax
    79f4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    79f8:	48 c1 f8 03          	sar    $0x3,%rax
    79fc:	48 01 c6             	add    %rax,%rsi
    79ff:	48 d1 fe             	sar    %rsi
    7a02:	74 14                	je     7a18 <register_tm_clones+0x38>
    7a04:	48 8b 05 dd c5 00 00 	mov    0xc5dd(%rip),%rax        # 13fe8 <_ITM_registerTMCloneTable@Base>
    7a0b:	48 85 c0             	test   %rax,%rax
    7a0e:	74 08                	je     7a18 <register_tm_clones+0x38>
    7a10:	ff e0                	jmp    *%rax
    7a12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    7a18:	c3                   	ret
    7a19:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000007a20 <__do_global_dtors_aux>:
    7a20:	f3 0f 1e fa          	endbr64
    7a24:	80 3d 7d e1 00 00 00 	cmpb   $0x0,0xe17d(%rip)        # 15ba8 <completed.0>
    7a2b:	75 2b                	jne    7a58 <__do_global_dtors_aux+0x38>
    7a2d:	55                   	push   %rbp
    7a2e:	48 83 3d ba c5 00 00 00 	cmpq   $0x0,0xc5ba(%rip)        # 13ff0 <__cxa_finalize@GLIBC_2.2.5>
    7a36:	48 89 e5             	mov    %rsp,%rbp
    7a39:	74 0c                	je     7a47 <__do_global_dtors_aux+0x27>
    7a3b:	48 8b 3d c6 c5 00 00 	mov    0xc5c6(%rip),%rdi        # 14008 <__dso_handle>
    7a42:	e8 e9 c9 ff ff       	call   4430 <__cxa_finalize@plt>
    7a47:	e8 64 ff ff ff       	call   79b0 <deregister_tm_clones>
    7a4c:	c6 05 55 e1 00 00 01 	movb   $0x1,0xe155(%rip)        # 15ba8 <completed.0>
    7a53:	5d                   	pop    %rbp
    7a54:	c3                   	ret
    7a55:	0f 1f 00             	nopl   (%rax)
    7a58:	c3                   	ret
    7a59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000007a60 <frame_dummy>:
    7a60:	f3 0f 1e fa          	endbr64
    7a64:	e9 77 ff ff ff       	jmp    79e0 <register_tm_clones>
    7a69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000007a70 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    7a70:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    7a74:	48 8d 87 28 01 00 00 	lea    0x128(%rdi),%rax
int do_protected_write(struct BarrierTask *data) {
    7a7b:	48 83 ec 08          	sub    $0x8,%rsp
  struct ProtectedState *protected = data->thread->protected_state;
    7a7f:	48 89 c2             	mov    %rax,%rdx
    7a82:	48 c1 ea 03          	shr    $0x3,%rdx
    7a86:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    7a8d:	0f 85 8e 00 00 00    	jne    7b21 <do_protected_write+0xb1>
    7a93:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    7a9a:	48 8d 50 48          	lea    0x48(%rax),%rdx
    7a9e:	48 89 d1             	mov    %rdx,%rcx
    7aa1:	48 c1 e9 03          	shr    $0x3,%rcx
    7aa5:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    7aac:	0f 85 8c 00 00 00    	jne    7b3e <do_protected_write+0xce>
  data->v++; // thread local
    7ab2:	48 8d 97 10 01 00 00 	lea    0x110(%rdi),%rdx
  struct ProtectedState *protected = data->thread->protected_state;
    7ab9:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    7abd:	48 89 d1             	mov    %rdx,%rcx
    7ac0:	48 c1 e9 03          	shr    $0x3,%rcx
    7ac4:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    7acb:	75 69                	jne    7b36 <do_protected_write+0xc6>
  protected->protected++; // shared between all threads
    7acd:	48 89 c2             	mov    %rax,%rdx
  data->v++; // thread local
    7ad0:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  protected->protected++; // shared between all threads
    7ad8:	48 c1 ea 03          	shr    $0x3,%rdx
    7adc:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    7ae3:	75 49                	jne    7b2e <do_protected_write+0xbe>
  if (protected->balance > 0) {
    7ae5:	48 8d 78 08          	lea    0x8(%rax),%rdi
  protected->protected++; // shared between all threads
    7ae9:	48 83 00 01          	addq   $0x1,(%rax)
  if (protected->balance > 0) {
    7aed:	48 89 fa             	mov    %rdi,%rdx
    7af0:	48 c1 ea 03          	shr    $0x3,%rdx
    7af4:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    7afb:	75 2c                	jne    7b29 <do_protected_write+0xb9>
    7afd:	48 8b 48 08          	mov    0x8(%rax),%rcx
    protected->balance -= 500; // shared between all threads
    7b01:	48 85 c9             	test   %rcx,%rcx
    7b04:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    7b0b:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    7b12:	48 0f 4f d6          	cmovg  %rsi,%rdx
    7b16:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    7b1a:	31 c0                	xor    %eax,%eax
    7b1c:	48 83 c4 08          	add    $0x8,%rsp
    7b20:	c3                   	ret
  struct ProtectedState *protected = data->thread->protected_state;
    7b21:	48 89 c7             	mov    %rax,%rdi
    7b24:	e8 b7 c9 ff ff       	call   44e0 <__asan_report_load8@plt>
  if (protected->balance > 0) {
    7b29:	e8 b2 c9 ff ff       	call   44e0 <__asan_report_load8@plt>
  protected->protected++; // shared between all threads
    7b2e:	48 89 c7             	mov    %rax,%rdi
    7b31:	e8 aa c9 ff ff       	call   44e0 <__asan_report_load8@plt>
  data->v++; // thread local
    7b36:	48 89 d7             	mov    %rdx,%rdi
    7b39:	e8 a2 c9 ff ff       	call   44e0 <__asan_report_load8@plt>
  struct ProtectedState *protected = data->thread->protected_state;
    7b3e:	48 89 d7             	mov    %rdx,%rdi
    7b41:	e8 9a c9 ff ff       	call   44e0 <__asan_report_load8@plt>
    7b46:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000007b50 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    7b50:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    7b54:	48 8d 97 48 01 00 00 	lea    0x148(%rdi),%rdx
int barriered_reset(struct BarrierTask *data) {
    7b5b:	48 83 ec 08          	sub    $0x8,%rsp
    for (int x = 0 ; x < data->task_count ; x++) {
    7b5f:	48 89 d0             	mov    %rdx,%rax
    7b62:	48 c1 e8 03          	shr    $0x3,%rax
    7b66:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    7b6d:	84 c0                	test   %al,%al
    7b6f:	74 08                	je     7b79 <barriered_reset+0x29>
    7b71:	3c 03                	cmp    $0x3,%al
    7b73:	0f 8e 6b 01 00 00    	jle    7ce4 <barriered_reset+0x194>
    7b79:	48 63 97 48 01 00 00 	movslq 0x148(%rdi),%rdx
    7b80:	85 d2                	test   %edx,%edx
    7b82:	0f 8e 52 01 00 00    	jle    7cda <barriered_reset+0x18a>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    7b88:	48 8d 87 28 01 00 00 	lea    0x128(%rdi),%rax
    7b8f:	48 89 c1             	mov    %rax,%rcx
    7b92:	48 c1 e9 03          	shr    $0x3,%rcx
    7b96:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    7b9d:	0f 85 6e 01 00 00    	jne    7d11 <barriered_reset+0x1c1>
    7ba3:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    7baa:	48 8d 48 18          	lea    0x18(%rax),%rcx
    7bae:	48 89 ce             	mov    %rcx,%rsi
    7bb1:	48 c1 ee 03          	shr    $0x3,%rsi
    7bb5:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    7bbc:	0f 85 3f 01 00 00    	jne    7d01 <barriered_reset+0x1b1>
    7bc2:	48 8d b7 30 01 00 00 	lea    0x130(%rdi),%rsi
    7bc9:	4c 8b 40 18          	mov    0x18(%rax),%r8
    7bcd:	48 89 f1             	mov    %rsi,%rcx
    7bd0:	48 c1 e9 03          	shr    $0x3,%rcx
    7bd4:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    7bdb:	84 c9                	test   %cl,%cl
    7bdd:	74 09                	je     7be8 <barriered_reset+0x98>
    7bdf:	80 f9 03             	cmp    $0x3,%cl
    7be2:	0f 8e 21 01 00 00    	jle    7d09 <barriered_reset+0x1b9>
    7be8:	48 63 8f 30 01 00 00 	movslq 0x130(%rdi),%rcx
    7bef:	49 8d 3c c8          	lea    (%r8,%rcx,8),%rdi
    7bf3:	48 89 f9             	mov    %rdi,%rcx
    7bf6:	48 c1 e9 03          	shr    $0x3,%rcx
    7bfa:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    7c01:	0f 85 17 01 00 00    	jne    7d1e <barriered_reset+0x1ce>
    7c07:	48 8b 0f             	mov    (%rdi),%rcx
    7c0a:	48 8d 79 38          	lea    0x38(%rcx),%rdi
    7c0e:	48 89 fe             	mov    %rdi,%rsi
    7c11:	48 c1 ee 03          	shr    $0x3,%rsi
    7c15:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    7c1c:	0f 85 f7 00 00 00    	jne    7d19 <barriered_reset+0x1c9>
      data->thread->tasks[x].available = 1; 
    7c22:	48 8d 78 38          	lea    0x38(%rax),%rdi
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    7c26:	48 8b 49 38          	mov    0x38(%rcx),%rcx
      data->thread->tasks[x].available = 1; 
    7c2a:	48 89 fe             	mov    %rdi,%rsi
    7c2d:	48 c1 ee 03          	shr    $0x3,%rsi
    7c31:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    7c38:	0f 85 e5 00 00 00    	jne    7d23 <barriered_reset+0x1d3>
    7c3e:	48 8b 40 38          	mov    0x38(%rax),%rax
    7c42:	48 c1 e2 09          	shl    $0x9,%rdx
    7c46:	48 8d b9 80 00 00 00 	lea    0x80(%rcx),%rdi
    7c4d:	48 8d b4 11 80 00 00 00 	lea    0x80(%rcx,%rdx,1),%rsi
    7c55:	48 05 44 01 00 00    	add    $0x144,%rax
    7c5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    7c60:	48 89 fa             	mov    %rdi,%rdx
    7c63:	48 c1 ea 03          	shr    $0x3,%rdx
    7c67:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    7c6e:	84 d2                	test   %dl,%dl
    7c70:	74 09                	je     7c7b <barriered_reset+0x12b>
    7c72:	80 fa 03             	cmp    $0x3,%dl
    7c75:	0f 8e 81 00 00 00    	jle    7cfc <barriered_reset+0x1ac>
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    7c7b:	48 8d 8f 80 00 00 00 	lea    0x80(%rdi),%rcx
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    7c82:	83 07 01             	addl   $0x1,(%rdi)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    7c85:	48 89 ca             	mov    %rcx,%rdx
    7c88:	48 c1 ea 03          	shr    $0x3,%rdx
    7c8c:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    7c93:	84 d2                	test   %dl,%dl
    7c95:	74 05                	je     7c9c <barriered_reset+0x14c>
    7c97:	80 fa 03             	cmp    $0x3,%dl
    7c9a:	7e 58                	jle    7cf4 <barriered_reset+0x1a4>
      data->thread->tasks[x].available = 1; 
    7c9c:	48 89 c2             	mov    %rax,%rdx
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    7c9f:	83 87 80 00 00 00 01 	addl   $0x1,0x80(%rdi)
      data->thread->tasks[x].available = 1; 
    7ca6:	48 c1 ea 03          	shr    $0x3,%rdx
    7caa:	0f b6 8a 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%ecx
    7cb1:	48 89 c2             	mov    %rax,%rdx
    7cb4:	83 e2 07             	and    $0x7,%edx
    7cb7:	83 c2 03             	add    $0x3,%edx
    7cba:	38 ca                	cmp    %cl,%dl
    7cbc:	7c 04                	jl     7cc2 <barriered_reset+0x172>
    7cbe:	84 c9                	test   %cl,%cl
    7cc0:	75 2a                	jne    7cec <barriered_reset+0x19c>
    for (int x = 0 ; x < data->task_count ; x++) {
    7cc2:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
      data->thread->tasks[x].available = 1; 
    7cc9:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    for (int x = 0 ; x < data->task_count ; x++) {
    7ccf:	48 05 00 02 00 00    	add    $0x200,%rax
    7cd5:	48 39 f7             	cmp    %rsi,%rdi
    7cd8:	75 86                	jne    7c60 <barriered_reset+0x110>
  asm volatile ("sfence" ::: "memory");
    7cda:	0f ae f8             	sfence
}
    7cdd:	31 c0                	xor    %eax,%eax
    7cdf:	48 83 c4 08          	add    $0x8,%rsp
    7ce3:	c3                   	ret
    for (int x = 0 ; x < data->task_count ; x++) {
    7ce4:	48 89 d7             	mov    %rdx,%rdi
    7ce7:	e8 64 c8 ff ff       	call   4550 <__asan_report_load4@plt>
      data->thread->tasks[x].available = 1; 
    7cec:	48 89 c7             	mov    %rax,%rdi
    7cef:	e8 cc c9 ff ff       	call   46c0 <__asan_report_store4@plt>
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    7cf4:	48 89 cf             	mov    %rcx,%rdi
    7cf7:	e8 54 c8 ff ff       	call   4550 <__asan_report_load4@plt>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    7cfc:	e8 4f c8 ff ff       	call   4550 <__asan_report_load4@plt>
    7d01:	48 89 cf             	mov    %rcx,%rdi
    7d04:	e8 d7 c7 ff ff       	call   44e0 <__asan_report_load8@plt>
    7d09:	48 89 f7             	mov    %rsi,%rdi
    7d0c:	e8 3f c8 ff ff       	call   4550 <__asan_report_load4@plt>
    7d11:	48 89 c7             	mov    %rax,%rdi
    7d14:	e8 c7 c7 ff ff       	call   44e0 <__asan_report_load8@plt>
    7d19:	e8 c2 c7 ff ff       	call   44e0 <__asan_report_load8@plt>
    7d1e:	e8 bd c7 ff ff       	call   44e0 <__asan_report_load8@plt>
      data->thread->tasks[x].available = 1; 
    7d23:	e8 b8 c7 ff ff       	call   44e0 <__asan_report_load8@plt>
    7d28:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000007d30 <external_thread>:
void * external_thread(void *arg) {
    7d30:	f3 0f 1e fa          	endbr64
    7d34:	41 57                	push   %r15
    7d36:	41 56                	push   %r14
    7d38:	49 89 fe             	mov    %rdi,%r14
  while (data->running == 1) {
    7d3b:	48 83 c7 44          	add    $0x44,%rdi
void * external_thread(void *arg) {
    7d3f:	41 55                	push   %r13
  while (data->running == 1) {
    7d41:	48 89 f8             	mov    %rdi,%rax
void * external_thread(void *arg) {
    7d44:	41 54                	push   %r12
  while (data->running == 1) {
    7d46:	48 c1 e8 03          	shr    $0x3,%rax
void * external_thread(void *arg) {
    7d4a:	55                   	push   %rbp
    7d4b:	53                   	push   %rbx
    7d4c:	48 83 ec 08          	sub    $0x8,%rsp
  while (data->running == 1) {
    7d50:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    7d57:	48 89 f8             	mov    %rdi,%rax
    7d5a:	83 e0 07             	and    $0x7,%eax
    7d5d:	83 c0 03             	add    $0x3,%eax
    7d60:	38 d0                	cmp    %dl,%al
    7d62:	7c 08                	jl     7d6c <external_thread+0x3c>
    7d64:	84 d2                	test   %dl,%dl
    7d66:	0f 85 4d 03 00 00    	jne    80b9 <external_thread+0x389>
    7d6c:	41 83 7e 44 01       	cmpl   $0x1,0x44(%r14)
    7d71:	0f 85 27 01 00 00    	jne    7e9e <external_thread+0x16e>
    for (int b = 0; b < data->buffers_count; b++) {
    7d77:	49 8d be bc 00 00 00 	lea    0xbc(%r14),%rdi
    7d7e:	48 89 f8             	mov    %rdi,%rax
    7d81:	48 c1 e8 03          	shr    $0x3,%rax
    7d85:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    7d8c:	48 89 f8             	mov    %rdi,%rax
    7d8f:	83 e0 07             	and    $0x7,%eax
    7d92:	83 c0 03             	add    $0x3,%eax
    7d95:	38 d0                	cmp    %dl,%al
    7d97:	7c 08                	jl     7da1 <external_thread+0x71>
    7d99:	84 d2                	test   %dl,%dl
    7d9b:	0f 85 0b 03 00 00    	jne    80ac <external_thread+0x37c>
    7da1:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    7da8:	4d 8d 6e 50          	lea    0x50(%r14),%r13
    7dac:	0f 1f 40 00          	nopl   0x0(%rax)
    7db0:	85 f6                	test   %esi,%esi
    7db2:	0f 8e f7 00 00 00    	jle    7eaf <external_thread+0x17f>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    7db8:	4c 89 e8             	mov    %r13,%rax
    7dbb:	48 c1 e8 03          	shr    $0x3,%rax
    7dbf:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    7dc6:	0f 85 e5 02 00 00    	jne    80b1 <external_thread+0x381>
    7dcc:	4d 8b 5e 50          	mov    0x50(%r14),%r11
    7dd0:	45 31 e4             	xor    %r12d,%r12d
    7dd3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7dd8:	4e 8d 3c e5 00 00 00 00 	lea    0x0(,%r12,8),%r15
    7de0:	4b 8d 0c 3b          	lea    (%r11,%r15,1),%rcx
    7de4:	48 89 c8             	mov    %rcx,%rax
    7de7:	48 c1 e8 03          	shr    $0x3,%rax
    7deb:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    7df2:	0f 85 ac 02 00 00    	jne    80a4 <external_thread+0x374>
    7df8:	48 8b 01             	mov    (%rcx),%rax
    7dfb:	48 89 c2             	mov    %rax,%rdx
    7dfe:	48 c1 ea 03          	shr    $0x3,%rdx
    7e02:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    7e09:	84 d2                	test   %dl,%dl
    7e0b:	74 09                	je     7e16 <external_thread+0xe6>
    7e0d:	80 fa 03             	cmp    $0x3,%dl
    7e10:	0f 8e 86 02 00 00    	jle    809c <external_thread+0x36c>
    7e16:	44 8b 08             	mov    (%rax),%r9d
    7e19:	31 db                	xor    %ebx,%ebx
    7e1b:	4c 8d 50 08          	lea    0x8(%rax),%r10
    7e1f:	45 85 c9             	test   %r9d,%r9d
    7e22:	7e 62                	jle    7e86 <external_thread+0x156>
    7e24:	0f 1f 40 00          	nopl   0x0(%rax)
				if (data->buffers[b]->buffer[x].available == 0) {
    7e28:	4c 89 d2             	mov    %r10,%rdx
    7e2b:	48 c1 ea 03          	shr    $0x3,%rdx
    7e2f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    7e36:	0f 85 0d 02 00 00    	jne    8049 <external_thread+0x319>
    7e3c:	48 8b 78 08          	mov    0x8(%rax),%rdi
    7e40:	48 89 dd             	mov    %rbx,%rbp
    7e43:	48 c1 e5 08          	shl    $0x8,%rbp
    7e47:	48 01 ef             	add    %rbp,%rdi
    7e4a:	48 8d b7 80 00 00 00 	lea    0x80(%rdi),%rsi
    7e51:	48 89 f2             	mov    %rsi,%rdx
    7e54:	48 c1 ea 03          	shr    $0x3,%rdx
    7e58:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    7e5f:	84 d2                	test   %dl,%dl
    7e61:	74 09                	je     7e6c <external_thread+0x13c>
    7e63:	80 fa 03             	cmp    $0x3,%dl
    7e66:	0f 8e e5 01 00 00    	jle    8051 <external_thread+0x321>
    7e6c:	8b 97 80 00 00 00    	mov    0x80(%rdi),%edx
    7e72:	85 d2                	test   %edx,%edx
    7e74:	74 42                	je     7eb8 <external_thread+0x188>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    7e76:	48 83 c3 01          	add    $0x1,%rbx
    7e7a:	41 39 d9             	cmp    %ebx,%r9d
    7e7d:	7f a9                	jg     7e28 <external_thread+0xf8>
    for (int b = 0; b < data->buffers_count; b++) {
    7e7f:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    7e86:	49 83 c4 01          	add    $0x1,%r12
    7e8a:	44 39 e6             	cmp    %r12d,%esi
    7e8d:	0f 8f 45 ff ff ff    	jg     7dd8 <external_thread+0xa8>
  while (data->running == 1) {
    7e93:	41 83 7e 44 01       	cmpl   $0x1,0x44(%r14)
    7e98:	0f 84 12 ff ff ff    	je     7db0 <external_thread+0x80>
}
    7e9e:	48 83 c4 08          	add    $0x8,%rsp
    7ea2:	31 c0                	xor    %eax,%eax
    7ea4:	5b                   	pop    %rbx
    7ea5:	5d                   	pop    %rbp
    7ea6:	41 5c                	pop    %r12
    7ea8:	41 5d                	pop    %r13
    7eaa:	41 5e                	pop    %r14
    7eac:	41 5f                	pop    %r15
    7eae:	c3                   	ret
  while (data->running == 1) {
    7eaf:	eb fe                	jmp    7eaf <external_thread+0x17f>
    7eb1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    7eb8:	48 89 f8             	mov    %rdi,%rax
    7ebb:	48 c1 e8 03          	shr    $0x3,%rax
    7ebf:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    7ec6:	0f 85 cb 01 00 00    	jne    8097 <external_thread+0x367>
    7ecc:	48 8d 05 4d 81 00 00 	lea    0x814d(%rip),%rax        # 10020 <_IO_stdin_used+0x20>
    7ed3:	48 89 07             	mov    %rax,(%rdi)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    7ed6:	48 89 c8             	mov    %rcx,%rax
    7ed9:	48 c1 e8 03          	shr    $0x3,%rax
    7edd:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    7ee4:	0f 85 a0 01 00 00    	jne    808a <external_thread+0x35a>
    7eea:	48 8b 01             	mov    (%rcx),%rax
    7eed:	48 8d 78 08          	lea    0x8(%rax),%rdi
    7ef1:	48 89 fa             	mov    %rdi,%rdx
    7ef4:	48 c1 ea 03          	shr    $0x3,%rdx
    7ef8:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    7eff:	0f 85 8d 01 00 00    	jne    8092 <external_thread+0x362>
    7f05:	48 8b 48 08          	mov    0x8(%rax),%rcx
    7f09:	48 01 e9             	add    %rbp,%rcx
    7f0c:	48 8d b9 88 00 00 00 	lea    0x88(%rcx),%rdi
    7f13:	48 89 c8             	mov    %rcx,%rax
    7f16:	48 89 fa             	mov    %rdi,%rdx
    7f19:	48 c1 ea 03          	shr    $0x3,%rdx
    7f1d:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    7f24:	0f 85 2f 01 00 00    	jne    8059 <external_thread+0x329>
    7f2a:	48 8d b9 94 00 00 00 	lea    0x94(%rcx),%rdi
    7f31:	48 8b b1 88 00 00 00 	mov    0x88(%rcx),%rsi
    7f38:	48 89 fa             	mov    %rdi,%rdx
    7f3b:	48 c1 ea 03          	shr    $0x3,%rdx
    7f3f:	0f b6 8a 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%ecx
    7f46:	48 89 fa             	mov    %rdi,%rdx
    7f49:	83 e2 07             	and    $0x7,%edx
    7f4c:	83 c2 03             	add    $0x3,%edx
    7f4f:	38 ca                	cmp    %cl,%dl
    7f51:	7c 08                	jl     7f5b <external_thread+0x22b>
    7f53:	84 c9                	test   %cl,%cl
    7f55:	0f 85 03 01 00 00    	jne    805e <external_thread+0x32e>
    7f5b:	48 63 80 94 00 00 00 	movslq 0x94(%rax),%rax
    7f62:	bf 04 00 00 00       	mov    $0x4,%edi
    7f67:	48 c1 e0 05          	shl    $0x5,%rax
    7f6b:	48 01 c6             	add    %rax,%rsi
    7f6e:	e8 0d c5 ff ff       	call   4480 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    7f73:	4c 89 e8             	mov    %r13,%rax
    7f76:	48 c1 e8 03          	shr    $0x3,%rax
    7f7a:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    7f81:	0f 85 dc 00 00 00    	jne    8063 <external_thread+0x333>
    7f87:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    7f8b:	4c 01 ff             	add    %r15,%rdi
    7f8e:	48 89 f8             	mov    %rdi,%rax
    7f91:	48 c1 e8 03          	shr    $0x3,%rax
    7f95:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    7f9c:	0f 85 c9 00 00 00    	jne    806b <external_thread+0x33b>
    7fa2:	48 8b 07             	mov    (%rdi),%rax
    7fa5:	48 8d 78 08          	lea    0x8(%rax),%rdi
    7fa9:	48 89 fa             	mov    %rdi,%rdx
    7fac:	48 c1 ea 03          	shr    $0x3,%rdx
    7fb0:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    7fb7:	0f 85 b3 00 00 00    	jne    8070 <external_thread+0x340>
    7fbd:	48 03 68 08          	add    0x8(%rax),%rbp
    7fc1:	48 8d bd 80 00 00 00 	lea    0x80(%rbp),%rdi
    7fc8:	48 89 f8             	mov    %rdi,%rax
    7fcb:	48 c1 e8 03          	shr    $0x3,%rax
    7fcf:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    7fd6:	84 c0                	test   %al,%al
    7fd8:	74 08                	je     7fe2 <external_thread+0x2b2>
    7fda:	3c 03                	cmp    $0x3,%al
    7fdc:	0f 8e 93 00 00 00    	jle    8075 <external_thread+0x345>
    7fe2:	c7 85 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rbp)
          asm volatile ("sfence" ::: "memory");
    7fec:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    7fef:	4d 8b 5e 50          	mov    0x50(%r14),%r11
    7ff3:	4b 8d 0c 3b          	lea    (%r11,%r15,1),%rcx
    7ff7:	48 89 c8             	mov    %rcx,%rax
    7ffa:	48 c1 e8 03          	shr    $0x3,%rax
    7ffe:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    8005:	75 73                	jne    807a <external_thread+0x34a>
    8007:	48 8b 01             	mov    (%rcx),%rax
    800a:	48 89 c2             	mov    %rax,%rdx
    800d:	48 c1 ea 03          	shr    $0x3,%rdx
    8011:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    8018:	84 d2                	test   %dl,%dl
    801a:	74 05                	je     8021 <external_thread+0x2f1>
    801c:	80 fa 03             	cmp    $0x3,%dl
    801f:	7e 61                	jle    8082 <external_thread+0x352>
    8021:	44 8b 08             	mov    (%rax),%r9d
    8024:	48 83 c3 01          	add    $0x1,%rbx
    8028:	41 39 d9             	cmp    %ebx,%r9d
    802b:	0f 8e 4e fe ff ff    	jle    7e7f <external_thread+0x14f>
    8031:	4c 8d 50 08          	lea    0x8(%rax),%r10
				if (data->buffers[b]->buffer[x].available == 0) {
    8035:	4c 89 d2             	mov    %r10,%rdx
    8038:	48 c1 ea 03          	shr    $0x3,%rdx
    803c:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    8043:	0f 84 f3 fd ff ff    	je     7e3c <external_thread+0x10c>
    8049:	4c 89 d7             	mov    %r10,%rdi
    804c:	e8 8f c4 ff ff       	call   44e0 <__asan_report_load8@plt>
    8051:	48 89 f7             	mov    %rsi,%rdi
    8054:	e8 f7 c4 ff ff       	call   4550 <__asan_report_load4@plt>
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    8059:	e8 82 c4 ff ff       	call   44e0 <__asan_report_load8@plt>
    805e:	e8 ed c4 ff ff       	call   4550 <__asan_report_load4@plt>
					data->buffers[b]->buffer[x].available = 1;
    8063:	4c 89 ef             	mov    %r13,%rdi
    8066:	e8 75 c4 ff ff       	call   44e0 <__asan_report_load8@plt>
    806b:	e8 70 c4 ff ff       	call   44e0 <__asan_report_load8@plt>
    8070:	e8 6b c4 ff ff       	call   44e0 <__asan_report_load8@plt>
    8075:	e8 46 c6 ff ff       	call   46c0 <__asan_report_store4@plt>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    807a:	48 89 cf             	mov    %rcx,%rdi
    807d:	e8 5e c4 ff ff       	call   44e0 <__asan_report_load8@plt>
    8082:	48 89 c7             	mov    %rax,%rdi
    8085:	e8 c6 c4 ff ff       	call   4550 <__asan_report_load4@plt>
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    808a:	48 89 cf             	mov    %rcx,%rdi
    808d:	e8 4e c4 ff ff       	call   44e0 <__asan_report_load8@plt>
    8092:	e8 49 c4 ff ff       	call   44e0 <__asan_report_load8@plt>
					data->buffers[b]->buffer[x].data = "Hello world";
    8097:	e8 34 c6 ff ff       	call   46d0 <__asan_report_store8@plt>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    809c:	48 89 c7             	mov    %rax,%rdi
    809f:	e8 ac c4 ff ff       	call   4550 <__asan_report_load4@plt>
    80a4:	48 89 cf             	mov    %rcx,%rdi
    80a7:	e8 34 c4 ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int b = 0; b < data->buffers_count; b++) {
    80ac:	e8 9f c4 ff ff       	call   4550 <__asan_report_load4@plt>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    80b1:	4c 89 ef             	mov    %r13,%rdi
    80b4:	e8 27 c4 ff ff       	call   44e0 <__asan_report_load8@plt>
  while (data->running == 1) {
    80b9:	e8 92 c4 ff ff       	call   4550 <__asan_report_load4@plt>
    80be:	66 90                	xchg   %ax,%ax

00000000000080c0 <timer_thread>:
void* timer_thread(void *arg) {
    80c0:	f3 0f 1e fa          	endbr64
    80c4:	41 57                	push   %r15
    80c6:	41 56                	push   %r14
    80c8:	41 55                	push   %r13
    80ca:	49 89 fd             	mov    %rdi,%r13
    80cd:	41 54                	push   %r12
    80cf:	55                   	push   %rbp
    80d0:	53                   	push   %rbx
    80d1:	48 81 ec 28 01 00 00 	sub    $0x128,%rsp
    80d8:	8b 0d a2 da 00 00    	mov    0xdaa2(%rip),%ecx        # 15b80 <__asan_option_detect_stack_use_after_return@@Base>
    80de:	4c 8d 74 24 60       	lea    0x60(%rsp),%r14
    80e3:	4c 89 74 24 48       	mov    %r14,0x48(%rsp)
    80e8:	85 c9                	test   %ecx,%ecx
    80ea:	0f 85 fc 0c 00 00    	jne    8dec <timer_thread+0xd2c>
    80f0:	49 8d 86 c0 00 00 00 	lea    0xc0(%r14),%rax
  printf("In timer task %d\n", data->thread_index);
    80f7:	49 8d 7d 04          	lea    0x4(%r13),%rdi
void* timer_thread(void *arg) {
    80fb:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    8100:	48 8d 05 19 9e 00 00 	lea    0x9e19(%rip),%rax        # 11f20 <_IO_stdin_used+0x1f20>
    8107:	49 89 46 08          	mov    %rax,0x8(%r14)
    810b:	48 8d 05 ae ff ff ff 	lea    -0x52(%rip),%rax        # 80c0 <timer_thread>
    8112:	49 89 46 10          	mov    %rax,0x10(%r14)
    8116:	4c 89 f0             	mov    %r14,%rax
    8119:	48 c1 e8 03          	shr    $0x3,%rax
    811d:	49 c7 06 b3 8a b5 41 	movq   $0x41b58ab3,(%r14)
    8124:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    8129:	c7 80 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%rax)
    8133:	c7 80 04 80 ff 7f 00 00 f2 f2 	movl   $0xf2f20000,0x7fff8004(%rax)
    813d:	c7 80 08 80 ff 7f 00 00 f2 f2 	movl   $0xf2f20000,0x7fff8008(%rax)
    8147:	c7 80 0c 80 ff 7f 00 00 f2 f2 	movl   $0xf2f20000,0x7fff800c(%rax)
    8151:	c7 80 10 80 ff 7f 00 00 f3 f3 	movl   $0xf3f30000,0x7fff8010(%rax)
    815b:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    8164:	48 89 84 24 18 01 00 00 	mov    %rax,0x118(%rsp)
    816c:	31 c0                	xor    %eax,%eax
  printf("In timer task %d\n", data->thread_index);
    816e:	48 89 f8             	mov    %rdi,%rax
    8171:	48 c1 e8 03          	shr    $0x3,%rax
    8175:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    817c:	48 89 f8             	mov    %rdi,%rax
    817f:	83 e0 07             	and    $0x7,%eax
    8182:	83 c0 03             	add    $0x3,%eax
    8185:	38 d0                	cmp    %dl,%al
    8187:	7c 08                	jl     8191 <timer_thread+0xd1>
    8189:	84 d2                	test   %dl,%dl
    818b:	0f 85 56 0c 00 00    	jne    8de7 <timer_thread+0xd27>
    8191:	41 8b 55 04          	mov    0x4(%r13),%edx
    8195:	31 c0                	xor    %eax,%eax
    8197:	bf 01 00 00 00       	mov    $0x1,%edi
    819c:	48 8d 35 bd 7e 00 00 	lea    0x7ebd(%rip),%rsi        # 10060 <_IO_stdin_used+0x60>
    81a3:	e8 78 c3 ff ff       	call   4520 <__printf_chk@plt>
  struct timespec preempt = {
    81a8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    81ad:	4c 8d 78 80          	lea    -0x80(%rax),%r15
    81b1:	4c 89 f8             	mov    %r15,%rax
    81b4:	48 c1 e8 03          	shr    $0x3,%rax
    81b8:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    81bf:	0f 85 1a 0c 00 00    	jne    8ddf <timer_thread+0xd1f>
    81c5:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    81ca:	48 8d 78 88          	lea    -0x78(%rax),%rdi
    81ce:	48 c7 40 80 00 00 00 00 	movq   $0x0,-0x80(%rax)
    81d6:	48 89 f8             	mov    %rdi,%rax
    81d9:	48 c1 e8 03          	shr    $0x3,%rax
    81dd:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    81e4:	0f 85 f0 0b 00 00    	jne    8dda <timer_thread+0xd1a>
    81ea:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    81ef:	ba 88 13 00 00       	mov    $0x1388,%edx
  while (data->running && n < times) {
    81f4:	4d 8d 65 44          	lea    0x44(%r13),%r12
    81f8:	48 8d 35 a1 7e 00 00 	lea    0x7ea1(%rip),%rsi        # 100a0 <_IO_stdin_used+0xa0>
    81ff:	bf 01 00 00 00       	mov    $0x1,%edi
  struct timespec preempt = {
    8204:	48 c7 40 88 40 42 0f 00 	movq   $0xf4240,-0x78(%rax)
    820c:	31 c0                	xor    %eax,%eax
    820e:	e8 0d c3 ff ff       	call   4520 <__printf_chk@plt>
  while (data->running && n < times) {
    8213:	4c 89 e0             	mov    %r12,%rax
    8216:	48 c1 e8 03          	shr    $0x3,%rax
    821a:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    8221:	4c 89 e0             	mov    %r12,%rax
    8224:	83 e0 07             	and    $0x7,%eax
    8227:	83 c0 03             	add    $0x3,%eax
    822a:	38 d0                	cmp    %dl,%al
    822c:	7c 08                	jl     8236 <timer_thread+0x176>
    822e:	84 d2                	test   %dl,%dl
    8230:	0f 85 9c 0b 00 00    	jne    8dd2 <timer_thread+0xd12>
    8236:	41 8b 55 44          	mov    0x44(%r13),%edx
    823a:	85 d2                	test   %edx,%edx
    823c:	0f 84 18 02 00 00    	je     845a <timer_thread+0x39a>
    8242:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
        int next = (y + 1) % data->threads[x]->task_count;
    8247:	49 8d 6d 18          	lea    0x18(%r13),%rbp
    y++;
    824b:	4c 89 7c 24 40       	mov    %r15,0x40(%rsp)
  int y = 0;
    8250:	31 d2                	xor    %edx,%edx
    y++;
    8252:	4c 89 74 24 38       	mov    %r14,0x38(%rsp)
  int n = 0;
    8257:	31 db                	xor    %ebx,%ebx
    y++;
    8259:	41 89 d6             	mov    %edx,%r14d
    825c:	48 2d a0 00 00 00    	sub    $0xa0,%rax
    8262:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    8267:	49 8d 45 28          	lea    0x28(%r13),%rax
    826b:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    8270:	48 c1 e8 03          	shr    $0x3,%rax
    8274:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
        int next = (y + 1) % data->threads[x]->task_count;
    8279:	48 89 e8             	mov    %rbp,%rax
    827c:	48 c1 e8 03          	shr    $0x3,%rax
    8280:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    nanosleep(&preempt , &rem2);
    8285:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    828a:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    n++;
    828f:	83 c3 01             	add    $0x1,%ebx
    nanosleep(&preempt , &rem2);
    8292:	e8 49 c4 ff ff       	call   46e0 <nanosleep@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    8297:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    829c:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    82a3:	84 c0                	test   %al,%al
    82a5:	74 08                	je     82af <timer_thread+0x1ef>
    82a7:	3c 03                	cmp    $0x3,%al
    82a9:	0f 8e 19 0b 00 00    	jle    8dc8 <timer_thread+0xd08>
    82af:	49 63 45 28          	movslq 0x28(%r13),%rax
    y++;
    82b3:	45 8d 7e 01          	lea    0x1(%r14),%r15d
    for (int x = 0 ; x < data->thread_count ; x++) {
    82b7:	85 c0                	test   %eax,%eax
    82b9:	0f 8e 00 01 00 00    	jle    83bf <timer_thread+0x2ff>
        int next = (y + 1) % data->threads[x]->task_count;
    82bf:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    82c4:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    82cb:	0f 85 ef 0a 00 00    	jne    8dc0 <timer_thread+0xd00>
    82d1:	49 8b 7d 18          	mov    0x18(%r13),%rdi
        data->threads[x]->tasks[y].scheduled = 0;
    82d5:	4d 63 ce             	movslq %r14d,%r9
    82d8:	49 c1 e1 09          	shl    $0x9,%r9
    82dc:	4c 8d 14 c7          	lea    (%rdi,%rax,8),%r10
        int next = (y + 1) % data->threads[x]->task_count;
    82e0:	48 89 f8             	mov    %rdi,%rax
    82e3:	48 c1 e8 03          	shr    $0x3,%rax
    82e7:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    82ee:	0f 85 71 0a 00 00    	jne    8d65 <timer_thread+0xca5>
    82f4:	48 8b 0f             	mov    (%rdi),%rcx
    82f7:	48 8d 51 40          	lea    0x40(%rcx),%rdx
    82fb:	48 89 d0             	mov    %rdx,%rax
    82fe:	48 c1 e8 03          	shr    $0x3,%rax
    8302:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    8309:	84 c0                	test   %al,%al
    830b:	74 08                	je     8315 <timer_thread+0x255>
    830d:	3c 03                	cmp    $0x3,%al
    830f:	0f 8e 55 0a 00 00    	jle    8d6a <timer_thread+0xcaa>
    8315:	44 89 f8             	mov    %r15d,%eax
    8318:	99                   	cltd
    8319:	f7 79 40             	idivl  0x40(%rcx)
        data->threads[x]->tasks[next].scheduled = 1;
    831c:	48 8d 41 38          	lea    0x38(%rcx),%rax
    8320:	48 89 c6             	mov    %rax,%rsi
    8323:	48 c1 ee 03          	shr    $0x3,%rsi
    8327:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    832e:	0f 85 3e 0a 00 00    	jne    8d72 <timer_thread+0xcb2>
    8334:	48 8b 49 38          	mov    0x38(%rcx),%rcx
    8338:	48 63 d2             	movslq %edx,%rdx
    833b:	48 c1 e2 09          	shl    $0x9,%rdx
    833f:	48 8d 04 11          	lea    (%rcx,%rdx,1),%rax
    8343:	4c 8d 80 4c 01 00 00 	lea    0x14c(%rax),%r8
    834a:	4c 89 c2             	mov    %r8,%rdx
    834d:	48 c1 ea 03          	shr    $0x3,%rdx
    8351:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    8358:	4c 89 c2             	mov    %r8,%rdx
    835b:	83 e2 07             	and    $0x7,%edx
    835e:	83 c2 03             	add    $0x3,%edx
    8361:	40 38 f2             	cmp    %sil,%dl
    8364:	7c 09                	jl     836f <timer_thread+0x2af>
    8366:	40 84 f6             	test   %sil,%sil
    8369:	0f 85 0b 0a 00 00    	jne    8d7a <timer_thread+0xcba>
    836f:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    8379:	4c 01 c9             	add    %r9,%rcx
    837c:	48 8d 91 4c 01 00 00 	lea    0x14c(%rcx),%rdx
    8383:	48 89 d0             	mov    %rdx,%rax
    8386:	48 c1 e8 03          	shr    $0x3,%rax
    838a:	0f b6 b0 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%esi
    8391:	48 89 d0             	mov    %rdx,%rax
    8394:	83 e0 07             	and    $0x7,%eax
    8397:	83 c0 03             	add    $0x3,%eax
    839a:	40 38 f0             	cmp    %sil,%al
    839d:	7c 09                	jl     83a8 <timer_thread+0x2e8>
    839f:	40 84 f6             	test   %sil,%sil
    83a2:	0f 85 da 09 00 00    	jne    8d82 <timer_thread+0xcc2>
    83a8:	c7 81 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    83b2:	48 83 c7 08          	add    $0x8,%rdi
    83b6:	4c 39 d7             	cmp    %r10,%rdi
    83b9:	0f 85 21 ff ff ff    	jne    82e0 <timer_thread+0x220>
    asm volatile ("mfence" ::: "memory");
    83bf:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    83c2:	48 89 e8             	mov    %rbp,%rax
    83c5:	48 c1 e8 03          	shr    $0x3,%rax
    83c9:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    83d0:	0f 85 a1 0a 00 00    	jne    8e77 <timer_thread+0xdb7>
    83d6:	49 8b 7d 18          	mov    0x18(%r13),%rdi
    83da:	48 89 f8             	mov    %rdi,%rax
    83dd:	48 c1 e8 03          	shr    $0x3,%rax
    83e1:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    83e8:	0f 85 84 0a 00 00    	jne    8e72 <timer_thread+0xdb2>
    83ee:	48 8b 07             	mov    (%rdi),%rax
    83f1:	48 8d 78 40          	lea    0x40(%rax),%rdi
    83f5:	48 89 fa             	mov    %rdi,%rdx
    83f8:	48 c1 ea 03          	shr    $0x3,%rdx
    83fc:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    8403:	84 d2                	test   %dl,%dl
    8405:	74 09                	je     8410 <timer_thread+0x350>
    8407:	80 fa 03             	cmp    $0x3,%dl
    840a:	0f 8e 5d 0a 00 00    	jle    8e6d <timer_thread+0xdad>
    y++;
    8410:	45 31 f6             	xor    %r14d,%r14d
    8413:	44 39 78 40          	cmp    %r15d,0x40(%rax)
  while (data->running && n < times) {
    8417:	4c 89 e0             	mov    %r12,%rax
    y++;
    841a:	45 0f 4f f7          	cmovg  %r15d,%r14d
  while (data->running && n < times) {
    841e:	48 c1 e8 03          	shr    $0x3,%rax
    8422:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    8429:	4c 89 e0             	mov    %r12,%rax
    842c:	83 e0 07             	and    $0x7,%eax
    842f:	83 c0 03             	add    $0x3,%eax
    8432:	38 c8                	cmp    %cl,%al
    8434:	7c 08                	jl     843e <timer_thread+0x37e>
    8436:	84 c9                	test   %cl,%cl
    8438:	0f 85 62 09 00 00    	jne    8da0 <timer_thread+0xce0>
    843e:	41 8b 55 44          	mov    0x44(%r13),%edx
    8442:	85 d2                	test   %edx,%edx
    8444:	74 0c                	je     8452 <timer_thread+0x392>
    8446:	81 fb 88 13 00 00    	cmp    $0x1388,%ebx
    844c:	0f 85 33 fe ff ff    	jne    8285 <timer_thread+0x1c5>
    8452:	44 89 f2             	mov    %r14d,%edx
    8455:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    845a:	48 8d 3d 7f 7c 00 00 	lea    0x7c7f(%rip),%rdi        # 100e0 <_IO_stdin_used+0xe0>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    8461:	4d 8d 7d 30          	lea    0x30(%r13),%r15
    8465:	89 54 24 08          	mov    %edx,0x8(%rsp)
    8469:	e8 92 c3 ff ff       	call   4800 <puts@plt>
    846e:	4c 89 f8             	mov    %r15,%rax
    8471:	8b 54 24 08          	mov    0x8(%rsp),%edx
    8475:	48 c1 e8 03          	shr    $0x3,%rax
    8479:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    8480:	84 c0                	test   %al,%al
    8482:	74 08                	je     848c <timer_thread+0x3cc>
    8484:	3c 03                	cmp    $0x3,%al
    8486:	0f 8e 0c 09 00 00    	jle    8d98 <timer_thread+0xcd8>
    848c:	49 63 45 30          	movslq 0x30(%r13),%rax
    8490:	85 c0                	test   %eax,%eax
    8492:	0f 8e e2 00 00 00    	jle    857a <timer_thread+0x4ba>
    for (int y = 0 ; y < data->task_count ; y++) {
    8498:	49 8d 7d 40          	lea    0x40(%r13),%rdi
    849c:	48 89 f9             	mov    %rdi,%rcx
    849f:	48 c1 e9 03          	shr    $0x3,%rcx
    84a3:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    84aa:	84 c9                	test   %cl,%cl
    84ac:	74 09                	je     84b7 <timer_thread+0x3f7>
    84ae:	80 f9 03             	cmp    $0x3,%cl
    84b1:	0f 8e d3 08 00 00    	jle    8d8a <timer_thread+0xcca>
    84b7:	4d 63 4d 40          	movslq 0x40(%r13),%r9
    84bb:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
    84c3:	31 f6                	xor    %esi,%esi
    84c5:	4c 89 c9             	mov    %r9,%rcx
    84c8:	49 c1 e1 09          	shl    $0x9,%r9
    84cc:	85 c9                	test   %ecx,%ecx
    84ce:	0f 8e c7 04 00 00    	jle    899b <timer_thread+0x8db>
    84d4:	49 8d 45 18          	lea    0x18(%r13),%rax
    84d8:	49 81 c1 80 01 00 00 	add    $0x180,%r9
      data->threads[x]->tasks[y].sending = 0;
    84df:	49 89 c2             	mov    %rax,%r10
    84e2:	49 c1 ea 03          	shr    $0x3,%r10
    84e6:	41 80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r10)
    84ee:	0f 85 2b 0a 00 00    	jne    8f1f <timer_thread+0xe5f>
    84f4:	49 8b 7d 18          	mov    0x18(%r13),%rdi
    84f8:	48 01 f7             	add    %rsi,%rdi
    84fb:	48 89 f9             	mov    %rdi,%rcx
    84fe:	48 c1 e9 03          	shr    $0x3,%rcx
    8502:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    8509:	0f 85 0b 0a 00 00    	jne    8f1a <timer_thread+0xe5a>
    850f:	48 8b 0f             	mov    (%rdi),%rcx
    8512:	48 8d 79 38          	lea    0x38(%rcx),%rdi
    8516:	49 89 fb             	mov    %rdi,%r11
    8519:	49 c1 eb 03          	shr    $0x3,%r11
    851d:	41 80 bb 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r11)
    8525:	0f 85 ea 09 00 00    	jne    8f15 <timer_thread+0xe55>
    852b:	4c 8b 59 38          	mov    0x38(%rcx),%r11
    852f:	49 8d bb 80 01 00 00 	lea    0x180(%r11),%rdi
    8536:	4d 01 cb             	add    %r9,%r11
    8539:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    8540:	48 89 f9             	mov    %rdi,%rcx
    8543:	48 c1 e9 03          	shr    $0x3,%rcx
    8547:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    854e:	84 c9                	test   %cl,%cl
    8550:	74 09                	je     855b <timer_thread+0x49b>
    8552:	80 f9 03             	cmp    $0x3,%cl
    8555:	0f 8e b5 09 00 00    	jle    8f10 <timer_thread+0xe50>
    855b:	c7 07 00 00 00 00    	movl   $0x0,(%rdi)
    for (int y = 0 ; y < data->task_count ; y++) {
    8561:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    8568:	4c 39 df             	cmp    %r11,%rdi
    856b:	75 d3                	jne    8540 <timer_thread+0x480>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    856d:	48 83 c6 08          	add    $0x8,%rsi
    8571:	4c 39 c6             	cmp    %r8,%rsi
    8574:	0f 85 6c ff ff ff    	jne    84e6 <timer_thread+0x426>
  asm volatile ("mfence" ::: "memory");
    857a:	0f ae f0             	mfence
  struct timespec drain = {
    857d:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    8582:	48 83 e8 40          	sub    $0x40,%rax
    8586:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    858b:	48 c1 e8 03          	shr    $0x3,%rax
    858f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    8596:	0f 85 64 09 00 00    	jne    8f00 <timer_thread+0xe40>
    859c:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    85a1:	48 8d 78 c8          	lea    -0x38(%rax),%rdi
    85a5:	48 c7 40 c0 01 00 00 00 	movq   $0x1,-0x40(%rax)
    85ad:	48 89 f8             	mov    %rdi,%rax
    85b0:	48 c1 e8 03          	shr    $0x3,%rax
    85b4:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    85bb:	0f 85 3a 09 00 00    	jne    8efb <timer_thread+0xe3b>
    85c1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    85c6:	49 8d 5d 18          	lea    0x18(%r13),%rbx
    85ca:	4c 89 64 24 58       	mov    %r12,0x58(%rsp)
    85cf:	48 8d 2d 8a 7b 00 00 	lea    0x7b8a(%rip),%rbp        # 10160 <_IO_stdin_used+0x160>
    85d6:	4d 89 f4             	mov    %r14,%r12
    85d9:	41 89 d6             	mov    %edx,%r14d
    85dc:	48 c7 40 c8 00 00 00 00 	movq   $0x0,-0x38(%rax)
  while (drained == 0) {
    85e4:	49 8d 45 28          	lea    0x28(%r13),%rax
    85e8:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    85ed:	48 c1 e8 03          	shr    $0x3,%rax
    85f1:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
        int next = (y + 1) % data->threads[x]->task_count;
    85f6:	48 89 d8             	mov    %rbx,%rax
    85f9:	48 c1 e8 03          	shr    $0x3,%rax
    85fd:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    8602:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    8607:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    860e:	84 c0                	test   %al,%al
    8610:	74 08                	je     861a <timer_thread+0x55a>
    8612:	3c 03                	cmp    $0x3,%al
    8614:	0f 8e d7 08 00 00    	jle    8ef1 <timer_thread+0xe31>
    861a:	49 63 45 28          	movslq 0x28(%r13),%rax
    y++;
    861e:	45 8d 56 01          	lea    0x1(%r14),%r10d
    for (int x = 0 ; x < data->thread_count ; x++) {
    8622:	85 c0                	test   %eax,%eax
    8624:	0f 8e 09 01 00 00    	jle    8733 <timer_thread+0x673>
        int next = (y + 1) % data->threads[x]->task_count;
    862a:	48 8b 54 24 50       	mov    0x50(%rsp),%rdx
    862f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    8636:	0f 85 ad 08 00 00    	jne    8ee9 <timer_thread+0xe29>
    863c:	49 8b 7d 18          	mov    0x18(%r13),%rdi
        data->threads[x]->tasks[y].scheduled = 0;
    8640:	49 63 f6             	movslq %r14d,%rsi
    8643:	48 c1 e6 09          	shl    $0x9,%rsi
    8647:	4c 8d 0c c7          	lea    (%rdi,%rax,8),%r9
    864b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    8650:	48 89 f8             	mov    %rdi,%rax
    8653:	48 c1 e8 03          	shr    $0x3,%rax
    8657:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    865e:	0f 85 80 08 00 00    	jne    8ee4 <timer_thread+0xe24>
    8664:	48 8b 0f             	mov    (%rdi),%rcx
    8667:	48 8d 51 40          	lea    0x40(%rcx),%rdx
    866b:	48 89 d0             	mov    %rdx,%rax
    866e:	48 c1 e8 03          	shr    $0x3,%rax
    8672:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    8679:	84 c0                	test   %al,%al
    867b:	74 08                	je     8685 <timer_thread+0x5c5>
    867d:	3c 03                	cmp    $0x3,%al
    867f:	0f 8e 57 08 00 00    	jle    8edc <timer_thread+0xe1c>
    8685:	44 89 d0             	mov    %r10d,%eax
    8688:	99                   	cltd
    8689:	f7 79 40             	idivl  0x40(%rcx)
        data->threads[x]->tasks[next].scheduled = 1;
    868c:	48 8d 41 38          	lea    0x38(%rcx),%rax
    8690:	49 89 c0             	mov    %rax,%r8
    8693:	49 c1 e8 03          	shr    $0x3,%r8
    8697:	41 80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r8)
    869f:	0f 85 2f 08 00 00    	jne    8ed4 <timer_thread+0xe14>
    86a5:	48 8b 49 38          	mov    0x38(%rcx),%rcx
    86a9:	48 63 d2             	movslq %edx,%rdx
    86ac:	48 c1 e2 09          	shl    $0x9,%rdx
    86b0:	48 8d 04 11          	lea    (%rcx,%rdx,1),%rax
    86b4:	4c 8d 80 4c 01 00 00 	lea    0x14c(%rax),%r8
    86bb:	4c 89 c2             	mov    %r8,%rdx
    86be:	48 c1 ea 03          	shr    $0x3,%rdx
    86c2:	44 0f b6 9a 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%r11d
    86ca:	4c 89 c2             	mov    %r8,%rdx
    86cd:	83 e2 07             	and    $0x7,%edx
    86d0:	83 c2 03             	add    $0x3,%edx
    86d3:	44 38 da             	cmp    %r11b,%dl
    86d6:	7c 09                	jl     86e1 <timer_thread+0x621>
    86d8:	45 84 db             	test   %r11b,%r11b
    86db:	0f 85 eb 07 00 00    	jne    8ecc <timer_thread+0xe0c>
    86e1:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    86eb:	48 8d 04 31          	lea    (%rcx,%rsi,1),%rax
    86ef:	48 8d 90 4c 01 00 00 	lea    0x14c(%rax),%rdx
    86f6:	48 89 d1             	mov    %rdx,%rcx
    86f9:	48 c1 e9 03          	shr    $0x3,%rcx
    86fd:	44 0f b6 81 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%r8d
    8705:	48 89 d1             	mov    %rdx,%rcx
    8708:	83 e1 07             	and    $0x7,%ecx
    870b:	83 c1 03             	add    $0x3,%ecx
    870e:	44 38 c1             	cmp    %r8b,%cl
    8711:	7c 09                	jl     871c <timer_thread+0x65c>
    8713:	45 84 c0             	test   %r8b,%r8b
    8716:	0f 85 a8 07 00 00    	jne    8ec4 <timer_thread+0xe04>
    871c:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
    for (int x = 0 ; x < data->thread_count ; x++) {
    8726:	48 83 c7 08          	add    $0x8,%rdi
    872a:	4c 39 cf             	cmp    %r9,%rdi
    872d:	0f 85 1d ff ff ff    	jne    8650 <timer_thread+0x590>
    asm volatile ("mfence" ::: "memory");
    8733:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    8736:	48 89 d8             	mov    %rbx,%rax
    8739:	48 c1 e8 03          	shr    $0x3,%rax
    873d:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    8744:	0f 85 72 07 00 00    	jne    8ebc <timer_thread+0xdfc>
    874a:	49 8b 7d 18          	mov    0x18(%r13),%rdi
    874e:	48 89 f8             	mov    %rdi,%rax
    8751:	48 c1 e8 03          	shr    $0x3,%rax
    8755:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    875c:	0f 85 55 07 00 00    	jne    8eb7 <timer_thread+0xdf7>
    8762:	48 8b 07             	mov    (%rdi),%rax
    8765:	48 8d 78 40          	lea    0x40(%rax),%rdi
    8769:	48 89 fa             	mov    %rdi,%rdx
    876c:	48 c1 ea 03          	shr    $0x3,%rdx
    8770:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    8777:	84 d2                	test   %dl,%dl
    8779:	74 09                	je     8784 <timer_thread+0x6c4>
    877b:	80 fa 03             	cmp    $0x3,%dl
    877e:	0f 8e 2e 07 00 00    	jle    8eb2 <timer_thread+0xdf2>
    y++;
    8784:	44 39 50 40          	cmp    %r10d,0x40(%rax)
    8788:	b8 00 00 00 00       	mov    $0x0,%eax
    878d:	41 0f 4f c2          	cmovg  %r10d,%eax
    8791:	41 89 c6             	mov    %eax,%r14d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    8794:	4c 89 f8             	mov    %r15,%rax
    8797:	48 c1 e8 03          	shr    $0x3,%rax
    879b:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    87a2:	84 c0                	test   %al,%al
    87a4:	74 08                	je     87ae <timer_thread+0x6ee>
    87a6:	3c 03                	cmp    $0x3,%al
    87a8:	0f 8e e2 05 00 00    	jle    8d90 <timer_thread+0xcd0>
    87ae:	45 8b 4d 30          	mov    0x30(%r13),%r9d
    87b2:	45 85 c9             	test   %r9d,%r9d
    87b5:	0f 8e f5 01 00 00    	jle    89b0 <timer_thread+0x8f0>
    int all_empty = 1;
    87bb:	44 89 74 24 30       	mov    %r14d,0x30(%rsp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    87c0:	31 c0                	xor    %eax,%eax
    int all_empty = 1;
    87c2:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    87c8:	4c 89 64 24 38       	mov    %r12,0x38(%rsp)
    87cd:	0f 1f 00             	nopl   (%rax)
            all_empty = 0;
    87d0:	45 31 e4             	xor    %r12d,%r12d
    87d3:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    87d8:	4c 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%r14
    87e0:	4c 89 e8             	mov    %r13,%rax
    87e3:	4d 89 e5             	mov    %r12,%r13
    87e6:	49 89 c4             	mov    %rax,%r12
    87e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    87f0:	48 89 d8             	mov    %rbx,%rax
    87f3:	48 c1 e8 03          	shr    $0x3,%rax
    87f7:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    87fe:	0f 85 54 05 00 00    	jne    8d58 <timer_thread+0xc98>
    8804:	49 8b 7c 24 18       	mov    0x18(%r12),%rdi
    8809:	4c 01 f7             	add    %r14,%rdi
    880c:	48 89 f8             	mov    %rdi,%rax
    880f:	48 c1 e8 03          	shr    $0x3,%rax
    8813:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    881a:	0f 85 33 05 00 00    	jne    8d53 <timer_thread+0xc93>
    8820:	48 8b 17             	mov    (%rdi),%rdx
    8823:	48 8d 7a 38          	lea    0x38(%rdx),%rdi
    8827:	48 89 f8             	mov    %rdi,%rax
    882a:	48 c1 e8 03          	shr    $0x3,%rax
    882e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    8835:	0f 85 13 05 00 00    	jne    8d4e <timer_thread+0xc8e>
    883b:	4c 89 e8             	mov    %r13,%rax
    883e:	48 c1 e0 09          	shl    $0x9,%rax
    8842:	48 03 42 38          	add    0x38(%rdx),%rax
    8846:	48 8d b8 70 01 00 00 	lea    0x170(%rax),%rdi
    884d:	48 89 fa             	mov    %rdi,%rdx
    8850:	48 c1 ea 03          	shr    $0x3,%rdx
    8854:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    885b:	0f 85 e8 04 00 00    	jne    8d49 <timer_thread+0xc89>
    8861:	48 8b b8 70 01 00 00 	mov    0x170(%rax),%rdi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    8868:	31 d2                	xor    %edx,%edx
    886a:	eb 1d                	jmp    8889 <timer_thread+0x7c9>
    886c:	0f 1f 40 00          	nopl   0x0(%rax)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    8870:	4d 85 c0             	test   %r8,%r8
    8873:	0f 8f 85 00 00 00    	jg     88fe <timer_thread+0x83e>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    8879:	83 c2 01             	add    $0x1,%edx
    887c:	48 83 c7 28          	add    $0x28,%rdi
    8880:	44 39 ca             	cmp    %r9d,%edx
    8883:	0f 84 87 00 00 00    	je     8910 <timer_thread+0x850>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    8889:	48 89 f8             	mov    %rdi,%rax
    888c:	48 c1 e8 03          	shr    $0x3,%rax
    8890:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    8897:	0f 85 f9 00 00 00    	jne    8996 <timer_thread+0x8d6>
    889d:	48 8b 07             	mov    (%rdi),%rax
    88a0:	48 8d 70 08          	lea    0x8(%rax),%rsi
    88a4:	48 89 f1             	mov    %rsi,%rcx
    88a7:	48 c1 e9 03          	shr    $0x3,%rcx
    88ab:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    88b2:	0f 85 ce 00 00 00    	jne    8986 <timer_thread+0x8c6>
    88b8:	48 8d 77 08          	lea    0x8(%rdi),%rsi
    88bc:	48 8b 48 08          	mov    0x8(%rax),%rcx
    88c0:	48 89 f0             	mov    %rsi,%rax
    88c3:	48 c1 e8 03          	shr    $0x3,%rax
    88c7:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    88ce:	0f 85 aa 00 00 00    	jne    897e <timer_thread+0x8be>
    88d4:	48 8b 47 08          	mov    0x8(%rdi),%rax
    88d8:	48 8d 70 08          	lea    0x8(%rax),%rsi
    88dc:	49 89 f0             	mov    %rsi,%r8
    88df:	49 c1 e8 03          	shr    $0x3,%r8
    88e3:	41 80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r8)
    88eb:	0f 85 9d 00 00 00    	jne    898e <timer_thread+0x8ce>
    88f1:	4c 8b 40 08          	mov    0x8(%rax),%r8
    88f5:	48 85 c9             	test   %rcx,%rcx
    88f8:	0f 8e 72 ff ff ff    	jle    8870 <timer_thread+0x7b0>
    88fe:	48 89 ee             	mov    %rbp,%rsi
    8901:	bf 01 00 00 00       	mov    $0x1,%edi
    8906:	31 c0                	xor    %eax,%eax
    8908:	e8 13 bc ff ff       	call   4520 <__printf_chk@plt>
            all_empty = 0;
    890d:	45 31 d2             	xor    %r10d,%r10d
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    8910:	4c 89 f8             	mov    %r15,%rax
    8913:	48 c1 e8 03          	shr    $0x3,%rax
    8917:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    891e:	84 c0                	test   %al,%al
    8920:	74 08                	je     892a <timer_thread+0x86a>
    8922:	3c 03                	cmp    $0x3,%al
    8924:	0f 8e 17 04 00 00    	jle    8d41 <timer_thread+0xc81>
    892a:	45 8b 4c 24 30       	mov    0x30(%r12),%r9d
    892f:	49 83 c5 01          	add    $0x1,%r13
    8933:	45 39 e9             	cmp    %r13d,%r9d
    8936:	0f 8f b4 fe ff ff    	jg     87f0 <timer_thread+0x730>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    893c:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    8941:	4d 89 e5             	mov    %r12,%r13
    8944:	48 83 c0 01          	add    $0x1,%rax
    8948:	41 39 c1             	cmp    %eax,%r9d
    894b:	7e 09                	jle    8956 <timer_thread+0x896>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    894d:	45 85 c9             	test   %r9d,%r9d
    8950:	0f 8f 7a fe ff ff    	jg     87d0 <timer_thread+0x710>
    8956:	44 8b 74 24 30       	mov    0x30(%rsp),%r14d
    895b:	4c 8b 64 24 38       	mov    0x38(%rsp),%r12
    if (all_empty == 1) {
    8960:	41 83 fa 01          	cmp    $0x1,%r10d
    8964:	74 4a                	je     89b0 <timer_thread+0x8f0>
      nanosleep(&drain , &drainrem);
    8966:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    896b:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    8970:	48 8d 70 a0          	lea    -0x60(%rax),%rsi
    8974:	e8 67 bd ff ff       	call   46e0 <nanosleep@plt>
    8979:	e9 84 fc ff ff       	jmp    8602 <timer_thread+0x542>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    897e:	48 89 f7             	mov    %rsi,%rdi
    8981:	e8 5a bb ff ff       	call   44e0 <__asan_report_load8@plt>
    8986:	48 89 f7             	mov    %rsi,%rdi
    8989:	e8 52 bb ff ff       	call   44e0 <__asan_report_load8@plt>
    898e:	48 89 f7             	mov    %rsi,%rdi
    8991:	e8 4a bb ff ff       	call   44e0 <__asan_report_load8@plt>
    8996:	e8 45 bb ff ff       	call   44e0 <__asan_report_load8@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    899b:	48 83 c6 08          	add    $0x8,%rsi
    899f:	4c 39 c6             	cmp    %r8,%rsi
    89a2:	0f 85 24 fb ff ff    	jne    84cc <timer_thread+0x40c>
    89a8:	e9 cd fb ff ff       	jmp    857a <timer_thread+0x4ba>
    89ad:	0f 1f 00             	nopl   (%rax)
    89b0:	4d 89 e6             	mov    %r12,%r14
    89b3:	4c 8b 64 24 58       	mov    0x58(%rsp),%r12
    89b8:	48 8d 3d 61 77 00 00 	lea    0x7761(%rip),%rdi        # 10120 <_IO_stdin_used+0x120>
    89bf:	e8 3c be ff ff       	call   4800 <puts@plt>
  while (data->running) {
    89c4:	4c 89 e0             	mov    %r12,%rax
    89c7:	48 c1 e8 03          	shr    $0x3,%rax
    89cb:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    89d2:	4c 89 e0             	mov    %r12,%rax
    89d5:	83 e0 07             	and    $0x7,%eax
    89d8:	83 c0 03             	add    $0x3,%eax
    89db:	38 d0                	cmp    %dl,%al
    89dd:	7c 08                	jl     89e7 <timer_thread+0x927>
    89df:	84 d2                	test   %dl,%dl
    89e1:	0f 85 c9 03 00 00    	jne    8db0 <timer_thread+0xcf0>
    89e7:	41 8b 45 44          	mov    0x44(%r13),%eax
    89eb:	85 c0                	test   %eax,%eax
    89ed:	0f 84 41 02 00 00    	je     8c34 <timer_thread+0xb74>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    89f3:	49 8d 75 2c          	lea    0x2c(%r13),%rsi
    89f7:	48 89 f0             	mov    %rsi,%rax
    89fa:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    89ff:	48 c1 e8 03          	shr    $0x3,%rax
    8a03:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    8a0a:	48 89 f0             	mov    %rsi,%rax
    8a0d:	83 e0 07             	and    $0x7,%eax
    8a10:	83 c0 03             	add    $0x3,%eax
    8a13:	38 d0                	cmp    %dl,%al
    8a15:	7c 08                	jl     8a1f <timer_thread+0x95f>
    8a17:	84 d2                	test   %dl,%dl
    8a19:	0f 85 89 03 00 00    	jne    8da8 <timer_thread+0xce8>
    8a1f:	45 8b 55 2c          	mov    0x2c(%r13),%r10d
    8a23:	31 ed                	xor    %ebp,%ebp
    8a25:	45 85 d2             	test   %r10d,%r10d
    8a28:	0f 8e be 00 00 00    	jle    8aec <timer_thread+0xa2c>
    8a2e:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
      data->threads[x]->running = 0;
    8a33:	49 89 df             	mov    %rbx,%r15
    8a36:	49 c1 ef 03          	shr    $0x3,%r15
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    8a3a:	83 e0 07             	and    $0x7,%eax
    8a3d:	83 c0 03             	add    $0x3,%eax
    8a40:	88 44 24 28          	mov    %al,0x28(%rsp)
    8a44:	0f 1f 40 00          	nopl   0x0(%rax)
      data->threads[x]->running = 0;
    8a48:	41 80 bf 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r15)
    8a50:	0f 85 54 04 00 00    	jne    8eaa <timer_thread+0xdea>
    8a56:	49 8b 7d 18          	mov    0x18(%r13),%rdi
    8a5a:	48 8d 0c ed 00 00 00 00 	lea    0x0(,%rbp,8),%rcx
    8a62:	48 01 cf             	add    %rcx,%rdi
    8a65:	48 89 f8             	mov    %rdi,%rax
    8a68:	48 c1 e8 03          	shr    $0x3,%rax
    8a6c:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    8a73:	0f 85 2c 04 00 00    	jne    8ea5 <timer_thread+0xde5>
    8a79:	48 8b 07             	mov    (%rdi),%rax
    8a7c:	48 8d 78 44          	lea    0x44(%rax),%rdi
    8a80:	48 89 fa             	mov    %rdi,%rdx
    8a83:	48 c1 ea 03          	shr    $0x3,%rdx
    8a87:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    8a8e:	48 89 fa             	mov    %rdi,%rdx
    8a91:	83 e2 07             	and    $0x7,%edx
    8a94:	83 c2 03             	add    $0x3,%edx
    8a97:	40 38 f2             	cmp    %sil,%dl
    8a9a:	7c 09                	jl     8aa5 <timer_thread+0x9e5>
    8a9c:	40 84 f6             	test   %sil,%sil
    8a9f:	0f 85 fb 03 00 00    	jne    8ea0 <timer_thread+0xde0>
      if (data->threads[x]->type == IO) {
    8aa5:	48 8d 78 0c          	lea    0xc(%rax),%rdi
      data->threads[x]->running = 0;
    8aa9:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    8ab0:	48 89 fa             	mov    %rdi,%rdx
    8ab3:	48 c1 ea 03          	shr    $0x3,%rdx
    8ab7:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    8abe:	48 89 fa             	mov    %rdi,%rdx
    8ac1:	83 e2 07             	and    $0x7,%edx
    8ac4:	83 c2 03             	add    $0x3,%edx
    8ac7:	40 38 f2             	cmp    %sil,%dl
    8aca:	7c 09                	jl     8ad5 <timer_thread+0xa15>
    8acc:	40 84 f6             	test   %sil,%sil
    8acf:	0f 85 c6 03 00 00    	jne    8e9b <timer_thread+0xddb>
    8ad5:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
    8ad9:	0f 84 b1 01 00 00    	je     8c90 <timer_thread+0xbd0>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    8adf:	48 83 c5 01          	add    $0x1,%rbp
    8ae3:	41 39 ea             	cmp    %ebp,%r10d
    8ae6:	0f 8f 5c ff ff ff    	jg     8a48 <timer_thread+0x988>
    for (int x = 0 ; x < data->thread_count ; x++) {
    8aec:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    8af1:	48 c1 e8 03          	shr    $0x3,%rax
    8af5:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    8afc:	84 c0                	test   %al,%al
    8afe:	74 08                	je     8b08 <timer_thread+0xa48>
    8b00:	3c 03                	cmp    $0x3,%al
    8b02:	0f 8e 89 03 00 00    	jle    8e91 <timer_thread+0xdd1>
    8b08:	49 63 45 28          	movslq 0x28(%r13),%rax
    8b0c:	85 c0                	test   %eax,%eax
    8b0e:	0f 8e e6 00 00 00    	jle    8bfa <timer_thread+0xb3a>
      for (int y = 0 ; y < data->task_count ; y++) {
    8b14:	49 8d 7d 40          	lea    0x40(%r13),%rdi
    8b18:	48 89 fa             	mov    %rdi,%rdx
    8b1b:	48 c1 ea 03          	shr    $0x3,%rdx
    8b1f:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    8b26:	84 d2                	test   %dl,%dl
    8b28:	74 09                	je     8b33 <timer_thread+0xa73>
    8b2a:	80 fa 03             	cmp    $0x3,%dl
    8b2d:	0f 8e 59 03 00 00    	jle    8e8c <timer_thread+0xdcc>
    8b33:	4d 63 4d 40          	movslq 0x40(%r13),%r9
    8b37:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
    8b3f:	31 f6                	xor    %esi,%esi
    8b41:	4c 89 ca             	mov    %r9,%rdx
    8b44:	49 c1 e1 09          	shl    $0x9,%r9
    8b48:	85 d2                	test   %edx,%edx
    8b4a:	0f 8e df 01 00 00    	jle    8d2f <timer_thread+0xc6f>
        data->threads[x]->tasks[y].scheduled = 0;
    8b50:	49 89 da             	mov    %rbx,%r10
    8b53:	49 81 c1 4c 01 00 00 	add    $0x14c,%r9
    8b5a:	49 c1 ea 03          	shr    $0x3,%r10
    8b5e:	66 90                	xchg   %ax,%ax
    8b60:	41 80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r10)
    8b68:	0f 85 16 03 00 00    	jne    8e84 <timer_thread+0xdc4>
    8b6e:	49 8b 7d 18          	mov    0x18(%r13),%rdi
    8b72:	48 01 f7             	add    %rsi,%rdi
    8b75:	48 89 f8             	mov    %rdi,%rax
    8b78:	48 c1 e8 03          	shr    $0x3,%rax
    8b7c:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    8b83:	0f 85 f6 02 00 00    	jne    8e7f <timer_thread+0xdbf>
    8b89:	48 8b 07             	mov    (%rdi),%rax
    8b8c:	48 8d 78 38          	lea    0x38(%rax),%rdi
    8b90:	48 89 fa             	mov    %rdi,%rdx
    8b93:	48 c1 ea 03          	shr    $0x3,%rdx
    8b97:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    8b9e:	0f 85 c4 02 00 00    	jne    8e68 <timer_thread+0xda8>
    8ba4:	48 8b 48 38          	mov    0x38(%rax),%rcx
    8ba8:	48 8d b9 4c 01 00 00 	lea    0x14c(%rcx),%rdi
    8baf:	4c 01 c9             	add    %r9,%rcx
    8bb2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    8bb8:	48 89 f8             	mov    %rdi,%rax
    8bbb:	48 c1 e8 03          	shr    $0x3,%rax
    8bbf:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    8bc6:	48 89 f8             	mov    %rdi,%rax
    8bc9:	83 e0 07             	and    $0x7,%eax
    8bcc:	83 c0 03             	add    $0x3,%eax
    8bcf:	38 d0                	cmp    %dl,%al
    8bd1:	7c 08                	jl     8bdb <timer_thread+0xb1b>
    8bd3:	84 d2                	test   %dl,%dl
    8bd5:	0f 85 85 01 00 00    	jne    8d60 <timer_thread+0xca0>
    8bdb:	c7 07 00 00 00 00    	movl   $0x0,(%rdi)
      for (int y = 0 ; y < data->task_count ; y++) {
    8be1:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    8be8:	48 39 f9             	cmp    %rdi,%rcx
    8beb:	75 cb                	jne    8bb8 <timer_thread+0xaf8>
    for (int x = 0 ; x < data->thread_count ; x++) {
    8bed:	48 83 c6 08          	add    $0x8,%rsi
    8bf1:	4c 39 c6             	cmp    %r8,%rsi
    8bf4:	0f 85 66 ff ff ff    	jne    8b60 <timer_thread+0xaa0>
    asm volatile ("mfence" ::: "memory");
    8bfa:	0f ae f0             	mfence
    8bfd:	48 8d 3d dc 75 00 00 	lea    0x75dc(%rip),%rdi        # 101e0 <_IO_stdin_used+0x1e0>
    8c04:	e8 f7 bb ff ff       	call   4800 <puts@plt>
    data->running = 0;
    8c09:	4c 89 e0             	mov    %r12,%rax
    8c0c:	48 c1 e8 03          	shr    $0x3,%rax
    8c10:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    8c17:	4c 89 e0             	mov    %r12,%rax
    8c1a:	83 e0 07             	and    $0x7,%eax
    8c1d:	83 c0 03             	add    $0x3,%eax
    8c20:	38 d0                	cmp    %dl,%al
    8c22:	7c 08                	jl     8c2c <timer_thread+0xb6c>
    8c24:	84 d2                	test   %dl,%dl
    8c26:	0f 85 34 02 00 00    	jne    8e60 <timer_thread+0xda0>
    8c2c:	41 c7 45 44 00 00 00 00 	movl   $0x0,0x44(%r13)
    8c34:	48 8d 3d e5 75 00 00 	lea    0x75e5(%rip),%rdi        # 10220 <_IO_stdin_used+0x220>
    8c3b:	e8 c0 bb ff ff       	call   4800 <puts@plt>
void* timer_thread(void *arg) {
    8c40:	4c 39 74 24 48       	cmp    %r14,0x48(%rsp)
    8c45:	0f 85 e1 01 00 00    	jne    8e2c <timer_thread+0xd6c>
    8c4b:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    8c50:	66 0f ef c0          	pxor   %xmm0,%xmm0
    8c54:	c7 80 10 80 ff 7f 00 00 00 00 	movl   $0x0,0x7fff8010(%rax)
    8c5e:	0f 11 80 00 80 ff 7f 	movups %xmm0,0x7fff8000(%rax)
}
    8c65:	48 8b 84 24 18 01 00 00 	mov    0x118(%rsp),%rax
    8c6d:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    8c76:	0f 85 ab 01 00 00    	jne    8e27 <timer_thread+0xd67>
    8c7c:	48 81 c4 28 01 00 00 	add    $0x128,%rsp
    8c83:	31 c0                	xor    %eax,%eax
    8c85:	5b                   	pop    %rbx
    8c86:	5d                   	pop    %rbp
    8c87:	41 5c                	pop    %r12
    8c89:	41 5d                	pop    %r13
    8c8b:	41 5e                	pop    %r14
    8c8d:	41 5f                	pop    %r15
    8c8f:	c3                   	ret
    8c90:	48 8d 3d 09 75 00 00 	lea    0x7509(%rip),%rdi        # 101a0 <_IO_stdin_used+0x1a0>
    8c97:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    8c9c:	e8 5f bb ff ff       	call   4800 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    8ca1:	41 80 bf 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r15)
    8ca9:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    8cae:	0f 85 6b 01 00 00    	jne    8e1f <timer_thread+0xd5f>
    8cb4:	49 03 4d 18          	add    0x18(%r13),%rcx
    8cb8:	48 89 c8             	mov    %rcx,%rax
    8cbb:	48 c1 e8 03          	shr    $0x3,%rax
    8cbf:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    8cc6:	0f 85 4b 01 00 00    	jne    8e17 <timer_thread+0xd57>
    8ccc:	48 8b 01             	mov    (%rcx),%rax
    8ccf:	48 8d 78 60          	lea    0x60(%rax),%rdi
    8cd3:	48 89 fa             	mov    %rdi,%rdx
    8cd6:	48 c1 ea 03          	shr    $0x3,%rdx
    8cda:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    8ce1:	84 d2                	test   %dl,%dl
    8ce3:	74 09                	je     8cee <timer_thread+0xc2e>
    8ce5:	80 fa 03             	cmp    $0x3,%dl
    8ce8:	0f 8e 24 01 00 00    	jle    8e12 <timer_thread+0xd52>
    8cee:	8b 78 60             	mov    0x60(%rax),%edi
    8cf1:	be 01 00 00 00       	mov    $0x1,%esi
    8cf6:	e8 f5 ba ff ff       	call   47f0 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    8cfb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    8d00:	48 c1 e8 03          	shr    $0x3,%rax
    8d04:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    8d0b:	38 44 24 28          	cmp    %al,0x28(%rsp)
    8d0f:	7c 08                	jl     8d19 <timer_thread+0xc59>
    8d11:	84 c0                	test   %al,%al
    8d13:	0f 85 ef 00 00 00    	jne    8e08 <timer_thread+0xd48>
    8d19:	45 8b 55 2c          	mov    0x2c(%r13),%r10d
    8d1d:	48 83 c5 01          	add    $0x1,%rbp
    8d21:	41 39 ea             	cmp    %ebp,%r10d
    8d24:	0f 8f 1e fd ff ff    	jg     8a48 <timer_thread+0x988>
    8d2a:	e9 bd fd ff ff       	jmp    8aec <timer_thread+0xa2c>
    for (int x = 0 ; x < data->thread_count ; x++) {
    8d2f:	48 83 c6 08          	add    $0x8,%rsi
    8d33:	49 39 f0             	cmp    %rsi,%r8
    8d36:	0f 85 0c fe ff ff    	jne    8b48 <timer_thread+0xa88>
    8d3c:	e9 b9 fe ff ff       	jmp    8bfa <timer_thread+0xb3a>
      for (int y = 0 ; y < data->my_thread_count ; y++) {
    8d41:	4c 89 ff             	mov    %r15,%rdi
    8d44:	e8 07 b8 ff ff       	call   4550 <__asan_report_load4@plt>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    8d49:	e8 92 b7 ff ff       	call   44e0 <__asan_report_load8@plt>
    8d4e:	e8 8d b7 ff ff       	call   44e0 <__asan_report_load8@plt>
    8d53:	e8 88 b7 ff ff       	call   44e0 <__asan_report_load8@plt>
    8d58:	48 89 df             	mov    %rbx,%rdi
    8d5b:	e8 80 b7 ff ff       	call   44e0 <__asan_report_load8@plt>
        data->threads[x]->tasks[y].scheduled = 0;
    8d60:	e8 5b b9 ff ff       	call   46c0 <__asan_report_store4@plt>
        int next = (y + 1) % data->threads[x]->task_count;
    8d65:	e8 76 b7 ff ff       	call   44e0 <__asan_report_load8@plt>
    8d6a:	48 89 d7             	mov    %rdx,%rdi
    8d6d:	e8 de b7 ff ff       	call   4550 <__asan_report_load4@plt>
        data->threads[x]->tasks[next].scheduled = 1;
    8d72:	48 89 c7             	mov    %rax,%rdi
    8d75:	e8 66 b7 ff ff       	call   44e0 <__asan_report_load8@plt>
    8d7a:	4c 89 c7             	mov    %r8,%rdi
    8d7d:	e8 3e b9 ff ff       	call   46c0 <__asan_report_store4@plt>
        data->threads[x]->tasks[y].scheduled = 0;
    8d82:	48 89 d7             	mov    %rdx,%rdi
    8d85:	e8 36 b9 ff ff       	call   46c0 <__asan_report_store4@plt>
    for (int y = 0 ; y < data->task_count ; y++) {
    8d8a:	e8 c1 b7 ff ff       	call   4550 <__asan_report_load4@plt>
    8d8f:	90                   	nop
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    8d90:	4c 89 ff             	mov    %r15,%rdi
    8d93:	e8 b8 b7 ff ff       	call   4550 <__asan_report_load4@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    8d98:	4c 89 ff             	mov    %r15,%rdi
    8d9b:	e8 b0 b7 ff ff       	call   4550 <__asan_report_load4@plt>
  while (data->running && n < times) {
    8da0:	4c 89 e7             	mov    %r12,%rdi
    8da3:	e8 a8 b7 ff ff       	call   4550 <__asan_report_load4@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    8da8:	48 89 f7             	mov    %rsi,%rdi
    8dab:	e8 a0 b7 ff ff       	call   4550 <__asan_report_load4@plt>
  while (data->running) {
    8db0:	4c 89 e7             	mov    %r12,%rdi
    8db3:	e8 98 b7 ff ff       	call   4550 <__asan_report_load4@plt>
    8db8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    8dc0:	48 89 ef             	mov    %rbp,%rdi
    8dc3:	e8 18 b7 ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    8dc8:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    8dcd:	e8 7e b7 ff ff       	call   4550 <__asan_report_load4@plt>
  while (data->running && n < times) {
    8dd2:	4c 89 e7             	mov    %r12,%rdi
    8dd5:	e8 76 b7 ff ff       	call   4550 <__asan_report_load4@plt>
  struct timespec preempt = {
    8dda:	e8 f1 b8 ff ff       	call   46d0 <__asan_report_store8@plt>
    8ddf:	4c 89 ff             	mov    %r15,%rdi
    8de2:	e8 e9 b8 ff ff       	call   46d0 <__asan_report_store8@plt>
  printf("In timer task %d\n", data->thread_index);
    8de7:	e8 64 b7 ff ff       	call   4550 <__asan_report_load4@plt>
void* timer_thread(void *arg) {
    8dec:	bf a0 00 00 00       	mov    $0xa0,%edi
    8df1:	e8 da b6 ff ff       	call   44d0 <__asan_stack_malloc_2@plt>
    8df6:	48 85 c0             	test   %rax,%rax
    8df9:	4c 0f 45 f0          	cmovne %rax,%r14
    8dfd:	e9 ee f2 ff ff       	jmp    80f0 <timer_thread+0x30>
    8e02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    8e08:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    8e0d:	e8 3e b7 ff ff       	call   4550 <__asan_report_load4@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    8e12:	e8 39 b7 ff ff       	call   4550 <__asan_report_load4@plt>
    8e17:	48 89 cf             	mov    %rcx,%rdi
    8e1a:	e8 c1 b6 ff ff       	call   44e0 <__asan_report_load8@plt>
    8e1f:	48 89 df             	mov    %rbx,%rdi
    8e22:	e8 b9 b6 ff ff       	call   44e0 <__asan_report_load8@plt>
}
    8e27:	e8 84 b8 ff ff       	call   46b0 <__stack_chk_fail@plt>
void* timer_thread(void *arg) {
    8e2c:	49 c7 06 0e 36 e0 45 	movq   $0x45e0360e,(%r14)
    8e33:	66 0f 6f 05 65 96 00 00 	movdqa 0x9665(%rip),%xmm0        # 124a0 <_IO_stdin_used+0x24a0>
    8e3b:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    8e40:	c7 80 10 80 ff 7f f5 f5 f5 f5 	movl   $0xf5f5f5f5,0x7fff8010(%rax)
    8e4a:	0f 11 80 00 80 ff 7f 	movups %xmm0,0x7fff8000(%rax)
    8e51:	49 8b 86 f8 00 00 00 	mov    0xf8(%r14),%rax
    8e58:	c6 00 00             	movb   $0x0,(%rax)
    8e5b:	e9 05 fe ff ff       	jmp    8c65 <timer_thread+0xba5>
    data->running = 0;
    8e60:	4c 89 e7             	mov    %r12,%rdi
    8e63:	e8 58 b8 ff ff       	call   46c0 <__asan_report_store4@plt>
        data->threads[x]->tasks[y].scheduled = 0;
    8e68:	e8 73 b6 ff ff       	call   44e0 <__asan_report_load8@plt>
    if (y >= data->threads[0]->task_count) {
    8e6d:	e8 de b6 ff ff       	call   4550 <__asan_report_load4@plt>
    8e72:	e8 69 b6 ff ff       	call   44e0 <__asan_report_load8@plt>
    8e77:	48 89 ef             	mov    %rbp,%rdi
    8e7a:	e8 61 b6 ff ff       	call   44e0 <__asan_report_load8@plt>
        data->threads[x]->tasks[y].scheduled = 0;
    8e7f:	e8 5c b6 ff ff       	call   44e0 <__asan_report_load8@plt>
    8e84:	48 89 df             	mov    %rbx,%rdi
    8e87:	e8 54 b6 ff ff       	call   44e0 <__asan_report_load8@plt>
      for (int y = 0 ; y < data->task_count ; y++) {
    8e8c:	e8 bf b6 ff ff       	call   4550 <__asan_report_load4@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    8e91:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    8e96:	e8 b5 b6 ff ff       	call   4550 <__asan_report_load4@plt>
      if (data->threads[x]->type == IO) {
    8e9b:	e8 b0 b6 ff ff       	call   4550 <__asan_report_load4@plt>
      data->threads[x]->running = 0;
    8ea0:	e8 1b b8 ff ff       	call   46c0 <__asan_report_store4@plt>
    8ea5:	e8 36 b6 ff ff       	call   44e0 <__asan_report_load8@plt>
    8eaa:	48 89 df             	mov    %rbx,%rdi
    8ead:	e8 2e b6 ff ff       	call   44e0 <__asan_report_load8@plt>
    if (y >= data->threads[0]->task_count) {
    8eb2:	e8 99 b6 ff ff       	call   4550 <__asan_report_load4@plt>
    8eb7:	e8 24 b6 ff ff       	call   44e0 <__asan_report_load8@plt>
    8ebc:	48 89 df             	mov    %rbx,%rdi
    8ebf:	e8 1c b6 ff ff       	call   44e0 <__asan_report_load8@plt>
        data->threads[x]->tasks[y].scheduled = 0;
    8ec4:	48 89 d7             	mov    %rdx,%rdi
    8ec7:	e8 f4 b7 ff ff       	call   46c0 <__asan_report_store4@plt>
        data->threads[x]->tasks[next].scheduled = 1;
    8ecc:	4c 89 c7             	mov    %r8,%rdi
    8ecf:	e8 ec b7 ff ff       	call   46c0 <__asan_report_store4@plt>
    8ed4:	48 89 c7             	mov    %rax,%rdi
    8ed7:	e8 04 b6 ff ff       	call   44e0 <__asan_report_load8@plt>
        int next = (y + 1) % data->threads[x]->task_count;
    8edc:	48 89 d7             	mov    %rdx,%rdi
    8edf:	e8 6c b6 ff ff       	call   4550 <__asan_report_load4@plt>
    8ee4:	e8 f7 b5 ff ff       	call   44e0 <__asan_report_load8@plt>
    8ee9:	48 89 df             	mov    %rbx,%rdi
    8eec:	e8 ef b5 ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    8ef1:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    8ef6:	e8 55 b6 ff ff       	call   4550 <__asan_report_load4@plt>
  struct timespec drain = {
    8efb:	e8 d0 b7 ff ff       	call   46d0 <__asan_report_store8@plt>
    8f00:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    8f05:	e8 c6 b7 ff ff       	call   46d0 <__asan_report_store8@plt>
    8f0a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->threads[x]->tasks[y].sending = 0;
    8f10:	e8 ab b7 ff ff       	call   46c0 <__asan_report_store4@plt>
    8f15:	e8 c6 b5 ff ff       	call   44e0 <__asan_report_load8@plt>
    8f1a:	e8 c1 b5 ff ff       	call   44e0 <__asan_report_load8@plt>
    8f1f:	48 89 c7             	mov    %rax,%rdi
    8f22:	e8 b9 b5 ff ff       	call   44e0 <__asan_report_load8@plt>
    8f27:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000008f30 <strtolower>:
void strtolower(char *str) {
    8f30:	f3 0f 1e fa          	endbr64
    8f34:	55                   	push   %rbp
    for (; *str; ++str)
    8f35:	48 89 f8             	mov    %rdi,%rax
    8f38:	48 89 fa             	mov    %rdi,%rdx
void strtolower(char *str) {
    8f3b:	53                   	push   %rbx
    for (; *str; ++str)
    8f3c:	48 c1 e8 03          	shr    $0x3,%rax
    8f40:	83 e2 07             	and    $0x7,%edx
void strtolower(char *str) {
    8f43:	48 89 fb             	mov    %rdi,%rbx
    8f46:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    8f4a:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    8f51:	38 d0                	cmp    %dl,%al
    8f53:	7f 08                	jg     8f5d <strtolower+0x2d>
    8f55:	84 c0                	test   %al,%al
    8f57:	0f 85 a7 00 00 00    	jne    9004 <strtolower+0xd4>
    8f5d:	48 0f be 2b          	movsbq (%rbx),%rbp
    8f61:	40 84 ed             	test   %bpl,%bpl
    8f64:	0f 84 93 00 00 00    	je     8ffd <strtolower+0xcd>
        *str = (char)tolower(*str);
    8f6a:	e8 81 b7 ff ff       	call   46f0 <__ctype_tolower_loc@plt>
    8f6f:	49 89 c0             	mov    %rax,%r8
    8f72:	48 89 c6             	mov    %rax,%rsi
    8f75:	49 c1 e8 03          	shr    $0x3,%r8
    8f79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    8f80:	41 80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r8)
    8f88:	0f 85 90 00 00 00    	jne    901e <strtolower+0xee>
    8f8e:	48 8b 06             	mov    (%rsi),%rax
    8f91:	48 8d 3c a8          	lea    (%rax,%rbp,4),%rdi
    8f95:	48 89 f8             	mov    %rdi,%rax
    8f98:	48 c1 e8 03          	shr    $0x3,%rax
    8f9c:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    8fa3:	48 89 f8             	mov    %rdi,%rax
    8fa6:	83 e0 07             	and    $0x7,%eax
    8fa9:	83 c0 03             	add    $0x3,%eax
    8fac:	38 d0                	cmp    %dl,%al
    8fae:	7c 04                	jl     8fb4 <strtolower+0x84>
    8fb0:	84 d2                	test   %dl,%dl
    8fb2:	75 65                	jne    9019 <strtolower+0xe9>
    8fb4:	48 89 d8             	mov    %rbx,%rax
    8fb7:	48 89 d9             	mov    %rbx,%rcx
    8fba:	8b 17                	mov    (%rdi),%edx
    8fbc:	48 c1 e8 03          	shr    $0x3,%rax
    8fc0:	83 e1 07             	and    $0x7,%ecx
    8fc3:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    8fca:	38 c8                	cmp    %cl,%al
    8fcc:	7f 04                	jg     8fd2 <strtolower+0xa2>
    8fce:	84 c0                	test   %al,%al
    8fd0:	75 3f                	jne    9011 <strtolower+0xe1>
    8fd2:	88 13                	mov    %dl,(%rbx)
    for (; *str; ++str)
    8fd4:	48 83 c3 01          	add    $0x1,%rbx
    8fd8:	48 89 d8             	mov    %rbx,%rax
    8fdb:	48 89 da             	mov    %rbx,%rdx
    8fde:	48 c1 e8 03          	shr    $0x3,%rax
    8fe2:	83 e2 07             	and    $0x7,%edx
    8fe5:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    8fec:	38 d0                	cmp    %dl,%al
    8fee:	7f 04                	jg     8ff4 <strtolower+0xc4>
    8ff0:	84 c0                	test   %al,%al
    8ff2:	75 15                	jne    9009 <strtolower+0xd9>
    8ff4:	48 0f be 2b          	movsbq (%rbx),%rbp
    8ff8:	40 84 ed             	test   %bpl,%bpl
    8ffb:	75 83                	jne    8f80 <strtolower+0x50>
}
    8ffd:	48 83 c4 08          	add    $0x8,%rsp
    9001:	5b                   	pop    %rbx
    9002:	5d                   	pop    %rbp
    9003:	c3                   	ret
    for (; *str; ++str)
    9004:	e8 87 b7 ff ff       	call   4790 <__asan_report_load1@plt>
    9009:	48 89 df             	mov    %rbx,%rdi
    900c:	e8 7f b7 ff ff       	call   4790 <__asan_report_load1@plt>
        *str = (char)tolower(*str);
    9011:	48 89 df             	mov    %rbx,%rdi
    9014:	e8 b7 b7 ff ff       	call   47d0 <__asan_report_store1@plt>
    9019:	e8 32 b5 ff ff       	call   4550 <__asan_report_load4@plt>
    901e:	48 89 f7             	mov    %rsi,%rdi
    9021:	e8 ba b4 ff ff       	call   44e0 <__asan_report_load8@plt>
    9026:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000009030 <zh_malloc>:
void *zh_malloc(size_t size) {
    9030:	f3 0f 1e fa          	endbr64
    9034:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    9038:	e8 53 b5 ff ff       	call   4590 <malloc@plt>
    if (!buf) {
    903d:	48 85 c0             	test   %rax,%rax
    9040:	74 05                	je     9047 <zh_malloc+0x17>
}
    9042:	48 83 c4 08          	add    $0x8,%rsp
    9046:	c3                   	ret
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    9047:	48 8d 3d 52 cb 00 00 	lea    0xcb52(%rip),%rdi        # 15ba0 <stderr@GLIBC_2.2.5>
    904e:	48 89 f8             	mov    %rdi,%rax
    9051:	48 c1 e8 03          	shr    $0x3,%rax
    9055:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    905c:	75 2c                	jne    908a <zh_malloc+0x5a>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    905e:	48 8b 0d 3b cb 00 00 	mov    0xcb3b(%rip),%rcx        # 15ba0 <stderr@GLIBC_2.2.5>
    9065:	ba 28 00 00 00       	mov    $0x28,%edx
    906a:	be 01 00 00 00       	mov    $0x1,%esi
    906f:	48 8d 3d ea 71 00 00 	lea    0x71ea(%rip),%rdi        # 10260 <_IO_stdin_used+0x260>
    9076:	e8 25 b4 ff ff       	call   44a0 <fwrite@plt>
        exit(1);
    907b:	e8 90 b5 ff ff       	call   4610 <__asan_handle_no_return@plt>
    9080:	bf 01 00 00 00       	mov    $0x1,%edi
    9085:	e8 86 b4 ff ff       	call   4510 <exit@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    908a:	e8 51 b4 ff ff       	call   44e0 <__asan_report_load8@plt>
    908f:	90                   	nop

0000000000009090 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    9090:	f3 0f 1e fa          	endbr64
    9094:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    9095:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    909a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    909d:	e8 fe b4 ff ff       	call   45a0 <strrchr@plt>
    if (!dot || dot == filename)
    90a2:	48 85 c0             	test   %rax,%rax
    90a5:	74 11                	je     90b8 <get_filename_ext+0x28>
    90a7:	48 39 c3             	cmp    %rax,%rbx
    90aa:	74 0c                	je     90b8 <get_filename_ext+0x28>
    return dot + 1;
    90ac:	48 83 c0 01          	add    $0x1,%rax
}
    90b0:	5b                   	pop    %rbx
    90b1:	c3                   	ret
    90b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    90b8:	48 8d 05 01 72 00 00 	lea    0x7201(%rip),%rax        # 102c0 <_IO_stdin_used+0x2c0>
}
    90bf:	5b                   	pop    %rbx
    90c0:	c3                   	ret
    90c1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    90cc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000090d0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    90d0:	f3 0f 1e fa          	endbr64
    90d4:	41 57                	push   %r15
    90d6:	41 56                	push   %r14
    90d8:	41 55                	push   %r13
    90da:	41 54                	push   %r12
    90dc:	55                   	push   %rbp
    90dd:	48 89 fd             	mov    %rdi,%rbp
    90e0:	53                   	push   %rbx
    90e1:	48 89 d3             	mov    %rdx,%rbx
    90e4:	48 81 ec 58 09 00 00 	sub    $0x958,%rsp
    90eb:	8b 05 8f ca 00 00    	mov    0xca8f(%rip),%eax        # 15b80 <__asan_option_detect_stack_use_after_return@@Base>
    90f1:	4c 8d 74 24 10       	lea    0x10(%rsp),%r14
    90f6:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    90fb:	4c 89 34 24          	mov    %r14,(%rsp)
    90ff:	85 c0                	test   %eax,%eax
    9101:	0f 85 31 06 00 00    	jne    9738 <send_headers+0x668>
    9107:	4d 89 f4             	mov    %r14,%r12
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    910a:	49 8d 7e 20          	lea    0x20(%r14),%rdi
    910e:	ba 00 04 00 00       	mov    $0x400,%edx
    9113:	48 89 ee             	mov    %rbp,%rsi
    9116:	48 8d 05 5b 8e 00 00 	lea    0x8e5b(%rip),%rax        # 11f78 <_IO_stdin_used+0x1f78>
    911d:	49 c1 ec 03          	shr    $0x3,%r12
    9121:	49 c7 06 b3 8a b5 41 	movq   $0x41b58ab3,(%r14)
    9128:	4d 8d be 40 09 00 00 	lea    0x940(%r14),%r15
    912f:	49 89 46 08          	mov    %rax,0x8(%r14)
    9133:	48 8d 05 96 ff ff ff 	lea    -0x6a(%rip),%rax        # 90d0 <send_headers>
    913a:	49 89 46 10          	mov    %rax,0x10(%r14)
    913e:	41 c7 84 24 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%r12)
    914a:	41 c7 84 24 84 80 ff 7f f2 f2 f2 f2 	movl   $0xf2f2f2f2,0x7fff8084(%r12)
    9156:	41 c7 84 24 88 80 ff 7f f2 f2 f2 f2 	movl   $0xf2f2f2f2,0x7fff8088(%r12)
    9162:	41 c7 84 24 8c 80 ff 7f f2 f2 f2 f2 	movl   $0xf2f2f2f2,0x7fff808c(%r12)
    916e:	41 c7 84 24 90 80 ff 7f f2 f2 f2 f2 	movl   $0xf2f2f2f2,0x7fff8090(%r12)
    917a:	41 c7 84 24 14 81 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff8114(%r12)
    9186:	41 c7 84 24 18 81 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff8118(%r12)
    9192:	41 c7 84 24 1c 81 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff811c(%r12)
    919e:	41 c7 84 24 20 81 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff8120(%r12)
    91aa:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    91b3:	48 89 84 24 48 09 00 00 	mov    %rax,0x948(%rsp)
    91bb:	31 c0                	xor    %eax,%eax
    91bd:	e8 ae b4 ff ff       	call   4670 <__strcpy_chk@plt>
    91c2:	48 89 c7             	mov    %rax,%rdi
    for (; *str; ++str)
    91c5:	48 c1 e8 03          	shr    $0x3,%rax
    91c9:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    91d0:	84 c0                	test   %al,%al
    91d2:	74 06                	je     91da <send_headers+0x10a>
    91d4:	0f 8e 47 05 00 00    	jle    9721 <send_headers+0x651>
    91da:	49 0f be af e0 f6 ff ff 	movsbq -0x920(%r15),%rbp
    91e2:	40 84 ed             	test   %bpl,%bpl
    91e5:	0f 84 a0 00 00 00    	je     928b <send_headers+0x1bb>
        *str = (char)tolower(*str);
    91eb:	e8 00 b5 ff ff       	call   46f0 <__ctype_tolower_loc@plt>
    91f0:	48 89 c2             	mov    %rax,%rdx
    91f3:	48 c1 ea 03          	shr    $0x3,%rdx
    91f7:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    91fe:	0f 85 10 06 00 00    	jne    9814 <send_headers+0x744>
    9204:	48 8b 08             	mov    (%rax),%rcx
    9207:	49 8d bf e0 f6 ff ff 	lea    -0x920(%r15),%rdi
    920e:	66 90                	xchg   %ax,%ax
    9210:	48 8d 04 a9          	lea    (%rcx,%rbp,4),%rax
    9214:	48 89 c2             	mov    %rax,%rdx
    9217:	48 c1 ea 03          	shr    $0x3,%rdx
    921b:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    9222:	48 89 c2             	mov    %rax,%rdx
    9225:	83 e2 07             	and    $0x7,%edx
    9228:	83 c2 03             	add    $0x3,%edx
    922b:	40 38 f2             	cmp    %sil,%dl
    922e:	7c 09                	jl     9239 <send_headers+0x169>
    9230:	40 84 f6             	test   %sil,%sil
    9233:	0f 85 ed 04 00 00    	jne    9726 <send_headers+0x656>
    9239:	8b 10                	mov    (%rax),%edx
    923b:	48 89 f8             	mov    %rdi,%rax
    923e:	48 89 fe             	mov    %rdi,%rsi
    9241:	48 c1 e8 03          	shr    $0x3,%rax
    9245:	83 e6 07             	and    $0x7,%esi
    9248:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    924f:	40 38 f0             	cmp    %sil,%al
    9252:	7f 08                	jg     925c <send_headers+0x18c>
    9254:	84 c0                	test   %al,%al
    9256:	0f 85 d7 04 00 00    	jne    9733 <send_headers+0x663>
    925c:	88 17                	mov    %dl,(%rdi)
    for (; *str; ++str)
    925e:	48 83 c7 01          	add    $0x1,%rdi
    9262:	48 89 f8             	mov    %rdi,%rax
    9265:	48 89 fa             	mov    %rdi,%rdx
    9268:	48 c1 e8 03          	shr    $0x3,%rax
    926c:	83 e2 07             	and    $0x7,%edx
    926f:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    9276:	38 d0                	cmp    %dl,%al
    9278:	7f 08                	jg     9282 <send_headers+0x1b2>
    927a:	84 c0                	test   %al,%al
    927c:	0f 85 ac 04 00 00    	jne    972e <send_headers+0x65e>
    9282:	48 0f be 2f          	movsbq (%rdi),%rbp
    9286:	40 84 ed             	test   %bpl,%bpl
    9289:	75 85                	jne    9210 <send_headers+0x140>
    void *buf = malloc(size);
    928b:	bf 11 00 00 00       	mov    $0x11,%edi
    9290:	e8 fb b2 ff ff       	call   4590 <malloc@plt>
    9295:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    9298:	48 85 c0             	test   %rax,%rax
    929b:	0f 84 80 05 00 00    	je     9821 <send_headers+0x751>
    iov[0].iov_base = zh_malloc(slen);
    92a1:	48 89 d8             	mov    %rbx,%rax
    92a4:	48 c1 e8 03          	shr    $0x3,%rax
    92a8:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    92af:	0f 85 e0 04 00 00    	jne    9795 <send_headers+0x6c5>
    iov[0].iov_len = slen;
    92b5:	48 8d 43 08          	lea    0x8(%rbx),%rax
    iov[0].iov_base = zh_malloc(slen);
    92b9:	48 89 3b             	mov    %rdi,(%rbx)
    iov[0].iov_len = slen;
    92bc:	48 89 c2             	mov    %rax,%rdx
    92bf:	48 c1 ea 03          	shr    $0x3,%rdx
    92c3:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    92ca:	0f 85 dd 04 00 00    	jne    97ad <send_headers+0x6dd>
    92d0:	48 c7 43 08 11 00 00 00 	movq   $0x11,0x8(%rbx)
  return __builtin___memcpy_chk (__dest, __src, __len,
    92d8:	ba 11 00 00 00       	mov    $0x11,%edx
    92dd:	48 8d 35 1c 70 00 00 	lea    0x701c(%rip),%rsi        # 10300 <_IO_stdin_used+0x300>
    92e4:	e8 d7 b1 ff ff       	call   44c0 <memcpy@plt>
    void *buf = malloc(size);
    92e9:	bf 17 00 00 00       	mov    $0x17,%edi
    92ee:	e8 9d b2 ff ff       	call   4590 <malloc@plt>
    92f3:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    92f6:	48 85 c0             	test   %rax,%rax
    92f9:	0f 84 f9 04 00 00    	je     97f8 <send_headers+0x728>
    iov[1].iov_base = zh_malloc(slen);
    92ff:	48 8d 43 10          	lea    0x10(%rbx),%rax
    9303:	48 89 c2             	mov    %rax,%rdx
    9306:	48 c1 ea 03          	shr    $0x3,%rdx
    930a:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    9311:	0f 85 8e 04 00 00    	jne    97a5 <send_headers+0x6d5>
    iov[1].iov_len = slen;
    9317:	48 8d 43 18          	lea    0x18(%rbx),%rax
    iov[1].iov_base = zh_malloc(slen);
    931b:	48 89 7b 10          	mov    %rdi,0x10(%rbx)
    iov[1].iov_len = slen;
    931f:	48 89 c2             	mov    %rax,%rdx
    9322:	48 c1 ea 03          	shr    $0x3,%rdx
    9326:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    932d:	0f 85 6a 04 00 00    	jne    979d <send_headers+0x6cd>
    9333:	48 c7 43 18 17 00 00 00 	movq   $0x17,0x18(%rbx)
    933b:	48 8d 35 fe 6f 00 00 	lea    0x6ffe(%rip),%rsi        # 10340 <_IO_stdin_used+0x340>
    9342:	ba 17 00 00 00       	mov    $0x17,%edx
    const char *dot = strrchr(filename, '.');
    9347:	49 8d af e0 f6 ff ff 	lea    -0x920(%r15),%rbp
    934e:	e8 6d b1 ff ff       	call   44c0 <memcpy@plt>
    9353:	be 2e 00 00 00       	mov    $0x2e,%esi
    9358:	48 89 ef             	mov    %rbp,%rdi
    935b:	e8 40 b2 ff ff       	call   45a0 <strrchr@plt>
    if (!dot || dot == filename)
    9360:	48 85 c0             	test   %rax,%rax
    9363:	0f 84 e7 02 00 00    	je     9650 <send_headers+0x580>
    9369:	48 39 e8             	cmp    %rbp,%rax
    936c:	0f 84 de 02 00 00    	je     9650 <send_headers+0x580>
    return dot + 1;
    9372:	48 8d 68 01          	lea    0x1(%rax),%rbp
    if (strcmp("jpg", file_ext) == 0)
    9376:	48 8d 3d 03 70 00 00 	lea    0x7003(%rip),%rdi        # 10380 <_IO_stdin_used+0x380>
    937d:	48 89 ee             	mov    %rbp,%rsi
    9380:	e8 ab b3 ff ff       	call   4730 <strcmp@plt>
    9385:	85 c0                	test   %eax,%eax
    9387:	0f 84 8b 02 00 00    	je     9618 <send_headers+0x548>
    if (strcmp("jpeg", file_ext) == 0)
    938d:	48 89 ee             	mov    %rbp,%rsi
    9390:	48 8d 3d 29 70 00 00 	lea    0x7029(%rip),%rdi        # 103c0 <_IO_stdin_used+0x3c0>
    9397:	4d 8d af 60 fb ff ff 	lea    -0x4a0(%r15),%r13
    939e:	e8 8d b3 ff ff       	call   4730 <strcmp@plt>
    93a3:	85 c0                	test   %eax,%eax
    93a5:	75 14                	jne    93bb <send_headers+0x2eb>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    93a7:	ba 1b 00 00 00       	mov    $0x1b,%edx
    93ac:	48 8d 35 4d 70 00 00 	lea    0x704d(%rip),%rsi        # 10400 <_IO_stdin_used+0x400>
    93b3:	4c 89 ef             	mov    %r13,%rdi
    93b6:	e8 05 b1 ff ff       	call   44c0 <memcpy@plt>
    if (strcmp("png", file_ext) == 0)
    93bb:	48 89 ee             	mov    %rbp,%rsi
    93be:	48 8d 3d 7b 70 00 00 	lea    0x707b(%rip),%rdi        # 10440 <_IO_stdin_used+0x440>
    93c5:	e8 66 b3 ff ff       	call   4730 <strcmp@plt>
    93ca:	85 c0                	test   %eax,%eax
    93cc:	75 14                	jne    93e2 <send_headers+0x312>
    93ce:	ba 1a 00 00 00       	mov    $0x1a,%edx
    93d3:	48 8d 35 a6 70 00 00 	lea    0x70a6(%rip),%rsi        # 10480 <_IO_stdin_used+0x480>
    93da:	4c 89 ef             	mov    %r13,%rdi
    93dd:	e8 de b0 ff ff       	call   44c0 <memcpy@plt>
    if (strcmp("gif", file_ext) == 0)
    93e2:	48 89 ee             	mov    %rbp,%rsi
    93e5:	48 8d 3d d4 70 00 00 	lea    0x70d4(%rip),%rdi        # 104c0 <_IO_stdin_used+0x4c0>
    93ec:	e8 3f b3 ff ff       	call   4730 <strcmp@plt>
    93f1:	85 c0                	test   %eax,%eax
    93f3:	0f 84 0f 03 00 00    	je     9708 <send_headers+0x638>
    if (strcmp("htm", file_ext) == 0)
    93f9:	48 89 ee             	mov    %rbp,%rsi
    93fc:	48 8d 3d 3d 71 00 00 	lea    0x713d(%rip),%rdi        # 10540 <_IO_stdin_used+0x540>
    9403:	e8 28 b3 ff ff       	call   4730 <strcmp@plt>
    9408:	85 c0                	test   %eax,%eax
    940a:	0f 84 d8 02 00 00    	je     96e8 <send_headers+0x618>
    if (strcmp("html", file_ext) == 0)
    9410:	48 89 ee             	mov    %rbp,%rsi
    9413:	48 8d 3d a6 71 00 00 	lea    0x71a6(%rip),%rdi        # 105c0 <_IO_stdin_used+0x5c0>
    941a:	e8 11 b3 ff ff       	call   4730 <strcmp@plt>
    941f:	85 c0                	test   %eax,%eax
    9421:	0f 84 a1 02 00 00    	je     96c8 <send_headers+0x5f8>
    if (strcmp("js", file_ext) == 0)
    9427:	48 89 ee             	mov    %rbp,%rsi
    942a:	48 8d 3d cf 71 00 00 	lea    0x71cf(%rip),%rdi        # 10600 <_IO_stdin_used+0x600>
    9431:	e8 fa b2 ff ff       	call   4730 <strcmp@plt>
    9436:	85 c0                	test   %eax,%eax
    9438:	0f 84 6a 02 00 00    	je     96a8 <send_headers+0x5d8>
    if (strcmp("css", file_ext) == 0)
    943e:	48 89 ee             	mov    %rbp,%rsi
    9441:	48 8d 3d 58 72 00 00 	lea    0x7258(%rip),%rdi        # 106a0 <_IO_stdin_used+0x6a0>
    9448:	e8 e3 b2 ff ff       	call   4730 <strcmp@plt>
    944d:	85 c0                	test   %eax,%eax
    944f:	0f 84 33 02 00 00    	je     9688 <send_headers+0x5b8>
    if (strcmp("txt", file_ext) == 0)
    9455:	48 89 ee             	mov    %rbp,%rsi
    9458:	48 8d 3d c1 72 00 00 	lea    0x72c1(%rip),%rdi        # 10720 <_IO_stdin_used+0x720>
    945f:	e8 cc b2 ff ff       	call   4730 <strcmp@plt>
    9464:	85 c0                	test   %eax,%eax
    9466:	0f 84 fc 01 00 00    	je     9668 <send_headers+0x598>
    slen = strlen(send_buffer);
    946c:	4c 89 ef             	mov    %r13,%rdi
    946f:	e8 6c b1 ff ff       	call   45e0 <strlen@plt>
    void *buf = malloc(size);
    9474:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    9477:	48 89 c5             	mov    %rax,%rbp
    void *buf = malloc(size);
    947a:	e8 11 b1 ff ff       	call   4590 <malloc@plt>
    947f:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    9482:	48 85 c0             	test   %rax,%rax
    9485:	0f 84 b2 03 00 00    	je     983d <send_headers+0x76d>
    iov[2].iov_base = zh_malloc(slen);
    948b:	48 8d 43 20          	lea    0x20(%rbx),%rax
    948f:	48 89 c2             	mov    %rax,%rdx
    9492:	48 c1 ea 03          	shr    $0x3,%rdx
    9496:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    949d:	0f 85 da 02 00 00    	jne    977d <send_headers+0x6ad>
    iov[2].iov_len = slen;
    94a3:	48 8d 43 28          	lea    0x28(%rbx),%rax
    iov[2].iov_base = zh_malloc(slen);
    94a7:	48 89 7b 20          	mov    %rdi,0x20(%rbx)
    iov[2].iov_len = slen;
    94ab:	48 89 c2             	mov    %rax,%rdx
    94ae:	48 c1 ea 03          	shr    $0x3,%rdx
    94b2:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    94b9:	0f 85 c6 02 00 00    	jne    9785 <send_headers+0x6b5>
    94bf:	48 89 6b 28          	mov    %rbp,0x28(%rbx)
  return __builtin___memcpy_chk (__dest, __src, __len,
    94c3:	48 89 ea             	mov    %rbp,%rdx
    94c6:	4c 89 ee             	mov    %r13,%rsi
    94c9:	e8 f2 af ff ff       	call   44c0 <memcpy@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    94ce:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    94d3:	4c 89 ef             	mov    %r13,%rdi
    94d6:	31 c0                	xor    %eax,%eax
    94d8:	48 8d 0d c1 72 00 00 	lea    0x72c1(%rip),%rcx        # 107a0 <_IO_stdin_used+0x7a0>
    94df:	ba 00 04 00 00       	mov    $0x400,%edx
    94e4:	be 01 00 00 00       	mov    $0x1,%esi
    94e9:	e8 32 b2 ff ff       	call   4720 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    94ee:	4c 89 ef             	mov    %r13,%rdi
    94f1:	e8 ea b0 ff ff       	call   45e0 <strlen@plt>
    void *buf = malloc(size);
    94f6:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    94f9:	48 89 c5             	mov    %rax,%rbp
    void *buf = malloc(size);
    94fc:	e8 8f b0 ff ff       	call   4590 <malloc@plt>
    9501:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    9504:	48 85 c0             	test   %rax,%rax
    9507:	0f 84 a8 02 00 00    	je     97b5 <send_headers+0x6e5>
    iov[3].iov_base = zh_malloc(slen);
    950d:	48 8d 43 30          	lea    0x30(%rbx),%rax
    9511:	48 89 c2             	mov    %rax,%rdx
    9514:	48 c1 ea 03          	shr    $0x3,%rdx
    9518:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    951f:	0f 85 68 02 00 00    	jne    978d <send_headers+0x6bd>
    iov[3].iov_len = slen;
    9525:	48 8d 43 38          	lea    0x38(%rbx),%rax
    iov[3].iov_base = zh_malloc(slen);
    9529:	48 89 7b 30          	mov    %rdi,0x30(%rbx)
    iov[3].iov_len = slen;
    952d:	48 89 c2             	mov    %rax,%rdx
    9530:	48 c1 ea 03          	shr    $0x3,%rdx
    9534:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    953b:	0f 85 0d 02 00 00    	jne    974e <send_headers+0x67e>
    9541:	48 89 6b 38          	mov    %rbp,0x38(%rbx)
    9545:	48 89 ea             	mov    %rbp,%rdx
    9548:	4c 89 ee             	mov    %r13,%rsi
    954b:	e8 70 af ff ff       	call   44c0 <memcpy@plt>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    9550:	4c 89 ef             	mov    %r13,%rdi
    9553:	ba 03 00 00 00       	mov    $0x3,%edx
    9558:	48 8d 35 81 72 00 00 	lea    0x7281(%rip),%rsi        # 107e0 <_IO_stdin_used+0x7e0>
    955f:	e8 5c af ff ff       	call   44c0 <memcpy@plt>
    void *buf = malloc(size);
    9564:	bf 02 00 00 00       	mov    $0x2,%edi
    9569:	e8 22 b0 ff ff       	call   4590 <malloc@plt>
    if (!buf) {
    956e:	48 85 c0             	test   %rax,%rax
    9571:	0f 84 e6 02 00 00    	je     985d <send_headers+0x78d>
    iov[4].iov_base = zh_malloc(slen);
    9577:	48 8d 7b 40          	lea    0x40(%rbx),%rdi
    957b:	48 89 fa             	mov    %rdi,%rdx
    957e:	48 c1 ea 03          	shr    $0x3,%rdx
    9582:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    9589:	0f 85 c7 01 00 00    	jne    9756 <send_headers+0x686>
    iov[4].iov_len = slen;
    958f:	48 8d 7b 48          	lea    0x48(%rbx),%rdi
    iov[4].iov_base = zh_malloc(slen);
    9593:	48 89 43 40          	mov    %rax,0x40(%rbx)
    iov[4].iov_len = slen;
    9597:	48 89 fa             	mov    %rdi,%rdx
    959a:	48 c1 ea 03          	shr    $0x3,%rdx
    959e:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    95a5:	0f 85 b0 01 00 00    	jne    975b <send_headers+0x68b>
  return __builtin___memcpy_chk (__dest, __src, __len,
    95ab:	41 0f b7 97 60 fb ff ff 	movzwl -0x4a0(%r15),%edx
    95b3:	48 c7 43 48 02 00 00 00 	movq   $0x2,0x48(%rbx)
    95bb:	66 89 10             	mov    %dx,(%rax)
void send_headers(const char *path, off_t len, struct iovec *iov) {
    95be:	4c 39 34 24          	cmp    %r14,(%rsp)
    95c2:	0f 85 98 01 00 00    	jne    9760 <send_headers+0x690>
    95c8:	41 c7 84 24 00 80 ff 7f 00 00 00 00 	movl   $0x0,0x7fff8000(%r12)
    95d4:	66 0f ef c0          	pxor   %xmm0,%xmm0
    95d8:	41 0f 11 84 24 84 80 ff 7f 	movups %xmm0,0x7fff8084(%r12)
    95e1:	41 0f 11 84 24 14 81 ff 7f 	movups %xmm0,0x7fff8114(%r12)
}
    95ea:	48 8b 84 24 48 09 00 00 	mov    0x948(%rsp),%rax
    95f2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    95fb:	0f 85 7c 02 00 00    	jne    987d <send_headers+0x7ad>
    9601:	48 81 c4 58 09 00 00 	add    $0x958,%rsp
    9608:	5b                   	pop    %rbx
    9609:	5d                   	pop    %rbp
    960a:	41 5c                	pop    %r12
    960c:	41 5d                	pop    %r13
    960e:	41 5e                	pop    %r14
    9610:	41 5f                	pop    %r15
    9612:	c3                   	ret
    9613:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    9618:	4d 8d af 60 fb ff ff 	lea    -0x4a0(%r15),%r13
    961f:	ba 1b 00 00 00       	mov    $0x1b,%edx
    9624:	48 8d 35 d5 6d 00 00 	lea    0x6dd5(%rip),%rsi        # 10400 <_IO_stdin_used+0x400>
    962b:	4c 89 ef             	mov    %r13,%rdi
    962e:	e8 8d ae ff ff       	call   44c0 <memcpy@plt>
    if (strcmp("jpeg", file_ext) == 0)
    9633:	48 89 ee             	mov    %rbp,%rsi
    9636:	48 8d 3d 83 6d 00 00 	lea    0x6d83(%rip),%rdi        # 103c0 <_IO_stdin_used+0x3c0>
    963d:	e8 ee b0 ff ff       	call   4730 <strcmp@plt>
    9642:	e9 5c fd ff ff       	jmp    93a3 <send_headers+0x2d3>
    9647:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        return "";
    9650:	48 8d 2d 69 6c 00 00 	lea    0x6c69(%rip),%rbp        # 102c0 <_IO_stdin_used+0x2c0>
    9657:	4d 8d af 60 fb ff ff 	lea    -0x4a0(%r15),%r13
    965e:	e9 7f fd ff ff       	jmp    93e2 <send_headers+0x312>
    9663:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    9668:	ba 1b 00 00 00       	mov    $0x1b,%edx
    966d:	48 8d 35 ec 70 00 00 	lea    0x70ec(%rip),%rsi        # 10760 <_IO_stdin_used+0x760>
    9674:	4c 89 ef             	mov    %r13,%rdi
    9677:	e8 44 ae ff ff       	call   44c0 <memcpy@plt>
    967c:	e9 eb fd ff ff       	jmp    946c <send_headers+0x39c>
    9681:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    9688:	ba 19 00 00 00       	mov    $0x19,%edx
    968d:	48 8d 35 4c 70 00 00 	lea    0x704c(%rip),%rsi        # 106e0 <_IO_stdin_used+0x6e0>
    9694:	4c 89 ef             	mov    %r13,%rdi
    9697:	e8 24 ae ff ff       	call   44c0 <memcpy@plt>
    969c:	e9 b4 fd ff ff       	jmp    9455 <send_headers+0x385>
    96a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    96a8:	ba 27 00 00 00       	mov    $0x27,%edx
    96ad:	48 8d 35 8c 6f 00 00 	lea    0x6f8c(%rip),%rsi        # 10640 <_IO_stdin_used+0x640>
    96b4:	4c 89 ef             	mov    %r13,%rdi
    96b7:	e8 04 ae ff ff       	call   44c0 <memcpy@plt>
    96bc:	e9 7d fd ff ff       	jmp    943e <send_headers+0x36e>
    96c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    96c8:	ba 1a 00 00 00       	mov    $0x1a,%edx
    96cd:	48 8d 35 ac 6e 00 00 	lea    0x6eac(%rip),%rsi        # 10580 <_IO_stdin_used+0x580>
    96d4:	4c 89 ef             	mov    %r13,%rdi
    96d7:	e8 e4 ad ff ff       	call   44c0 <memcpy@plt>
    96dc:	e9 46 fd ff ff       	jmp    9427 <send_headers+0x357>
    96e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    96e8:	ba 1a 00 00 00       	mov    $0x1a,%edx
    96ed:	48 8d 35 8c 6e 00 00 	lea    0x6e8c(%rip),%rsi        # 10580 <_IO_stdin_used+0x580>
    96f4:	4c 89 ef             	mov    %r13,%rdi
    96f7:	e8 c4 ad ff ff       	call   44c0 <memcpy@plt>
    96fc:	e9 0f fd ff ff       	jmp    9410 <send_headers+0x340>
    9701:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    9708:	ba 1a 00 00 00       	mov    $0x1a,%edx
    970d:	48 8d 35 ec 6d 00 00 	lea    0x6dec(%rip),%rsi        # 10500 <_IO_stdin_used+0x500>
    9714:	4c 89 ef             	mov    %r13,%rdi
    9717:	e8 a4 ad ff ff       	call   44c0 <memcpy@plt>
    971c:	e9 d8 fc ff ff       	jmp    93f9 <send_headers+0x329>
    for (; *str; ++str)
    9721:	e8 6a b0 ff ff       	call   4790 <__asan_report_load1@plt>
        *str = (char)tolower(*str);
    9726:	48 89 c7             	mov    %rax,%rdi
    9729:	e8 22 ae ff ff       	call   4550 <__asan_report_load4@plt>
    for (; *str; ++str)
    972e:	e8 5d b0 ff ff       	call   4790 <__asan_report_load1@plt>
        *str = (char)tolower(*str);
    9733:	e8 98 b0 ff ff       	call   47d0 <__asan_report_store1@plt>
void send_headers(const char *path, off_t len, struct iovec *iov) {
    9738:	bf 20 09 00 00       	mov    $0x920,%edi
    973d:	e8 fe ad ff ff       	call   4540 <__asan_stack_malloc_6@plt>
    9742:	48 85 c0             	test   %rax,%rax
    9745:	4c 0f 45 f0          	cmovne %rax,%r14
    9749:	e9 b9 f9 ff ff       	jmp    9107 <send_headers+0x37>
    iov[3].iov_len = slen;
    974e:	48 89 c7             	mov    %rax,%rdi
    9751:	e8 7a af ff ff       	call   46d0 <__asan_report_store8@plt>
    iov[4].iov_base = zh_malloc(slen);
    9756:	e8 75 af ff ff       	call   46d0 <__asan_report_store8@plt>
    iov[4].iov_len = slen;
    975b:	e8 70 af ff ff       	call   46d0 <__asan_report_store8@plt>
void send_headers(const char *path, off_t len, struct iovec *iov) {
    9760:	49 c7 06 0e 36 e0 45 	movq   $0x45e0360e,(%r14)
    9767:	48 8b 14 24          	mov    (%rsp),%rdx
    976b:	be 20 09 00 00       	mov    $0x920,%esi
    9770:	4c 89 f7             	mov    %r14,%rdi
    9773:	e8 98 af ff ff       	call   4710 <__asan_stack_free_6@plt>
    9778:	e9 6d fe ff ff       	jmp    95ea <send_headers+0x51a>
    iov[2].iov_base = zh_malloc(slen);
    977d:	48 89 c7             	mov    %rax,%rdi
    9780:	e8 4b af ff ff       	call   46d0 <__asan_report_store8@plt>
    iov[2].iov_len = slen;
    9785:	48 89 c7             	mov    %rax,%rdi
    9788:	e8 43 af ff ff       	call   46d0 <__asan_report_store8@plt>
    iov[3].iov_base = zh_malloc(slen);
    978d:	48 89 c7             	mov    %rax,%rdi
    9790:	e8 3b af ff ff       	call   46d0 <__asan_report_store8@plt>
    iov[0].iov_base = zh_malloc(slen);
    9795:	48 89 df             	mov    %rbx,%rdi
    9798:	e8 33 af ff ff       	call   46d0 <__asan_report_store8@plt>
    iov[1].iov_len = slen;
    979d:	48 89 c7             	mov    %rax,%rdi
    97a0:	e8 2b af ff ff       	call   46d0 <__asan_report_store8@plt>
    iov[1].iov_base = zh_malloc(slen);
    97a5:	48 89 c7             	mov    %rax,%rdi
    97a8:	e8 23 af ff ff       	call   46d0 <__asan_report_store8@plt>
    iov[0].iov_len = slen;
    97ad:	48 89 c7             	mov    %rax,%rdi
    97b0:	e8 1b af ff ff       	call   46d0 <__asan_report_store8@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    97b5:	48 8d 3d e4 c3 00 00 	lea    0xc3e4(%rip),%rdi        # 15ba0 <stderr@GLIBC_2.2.5>
    97bc:	48 89 f8             	mov    %rdi,%rax
    97bf:	48 c1 e8 03          	shr    $0x3,%rax
    97c3:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    97ca:	75 50                	jne    981c <send_headers+0x74c>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    97cc:	48 8b 0d cd c3 00 00 	mov    0xc3cd(%rip),%rcx        # 15ba0 <stderr@GLIBC_2.2.5>
    97d3:	ba 28 00 00 00       	mov    $0x28,%edx
    97d8:	be 01 00 00 00       	mov    $0x1,%esi
    97dd:	48 8d 3d 7c 6a 00 00 	lea    0x6a7c(%rip),%rdi        # 10260 <_IO_stdin_used+0x260>
    97e4:	e8 b7 ac ff ff       	call   44a0 <fwrite@plt>
        exit(1);
    97e9:	e8 22 ae ff ff       	call   4610 <__asan_handle_no_return@plt>
    97ee:	bf 01 00 00 00       	mov    $0x1,%edi
    97f3:	e8 18 ad ff ff       	call   4510 <exit@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    97f8:	48 8d 3d a1 c3 00 00 	lea    0xc3a1(%rip),%rdi        # 15ba0 <stderr@GLIBC_2.2.5>
    97ff:	48 89 f8             	mov    %rdi,%rax
    9802:	48 c1 e8 03          	shr    $0x3,%rax
    9806:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    980d:	74 bd                	je     97cc <send_headers+0x6fc>
    980f:	e8 cc ac ff ff       	call   44e0 <__asan_report_load8@plt>
        *str = (char)tolower(*str);
    9814:	48 89 c7             	mov    %rax,%rdi
    9817:	e8 c4 ac ff ff       	call   44e0 <__asan_report_load8@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    981c:	e8 bf ac ff ff       	call   44e0 <__asan_report_load8@plt>
    9821:	48 8d 3d 78 c3 00 00 	lea    0xc378(%rip),%rdi        # 15ba0 <stderr@GLIBC_2.2.5>
    9828:	48 89 f8             	mov    %rdi,%rax
    982b:	48 c1 e8 03          	shr    $0x3,%rax
    982f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    9836:	74 94                	je     97cc <send_headers+0x6fc>
    9838:	e8 a3 ac ff ff       	call   44e0 <__asan_report_load8@plt>
    983d:	48 8d 3d 5c c3 00 00 	lea    0xc35c(%rip),%rdi        # 15ba0 <stderr@GLIBC_2.2.5>
    9844:	48 89 f8             	mov    %rdi,%rax
    9847:	48 c1 e8 03          	shr    $0x3,%rax
    984b:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    9852:	0f 84 74 ff ff ff    	je     97cc <send_headers+0x6fc>
    9858:	e8 83 ac ff ff       	call   44e0 <__asan_report_load8@plt>
    985d:	48 8d 3d 3c c3 00 00 	lea    0xc33c(%rip),%rdi        # 15ba0 <stderr@GLIBC_2.2.5>
    9864:	48 89 f8             	mov    %rdi,%rax
    9867:	48 c1 e8 03          	shr    $0x3,%rax
    986b:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    9872:	0f 84 54 ff ff ff    	je     97cc <send_headers+0x6fc>
    9878:	e8 63 ac ff ff       	call   44e0 <__asan_report_load8@plt>
}
    987d:	e8 2e ae ff ff       	call   46b0 <__stack_chk_fail@plt>
    9882:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    988d:	0f 1f 00             	nopl   (%rax)

0000000000009890 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    9890:	f3 0f 1e fa          	endbr64
    9894:	41 55                	push   %r13
    9896:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    9899:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    989c:	41 54                	push   %r12
    989e:	55                   	push   %rbp
    989f:	48 89 f5             	mov    %rsi,%rbp
    98a2:	53                   	push   %rbx
    98a3:	48 89 d3             	mov    %rdx,%rbx
    98a6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    98aa:	e8 e1 ac ff ff       	call   4590 <malloc@plt>
    if (!buf) {
    98af:	48 85 c0             	test   %rax,%rax
    98b2:	0f 84 b3 00 00 00    	je     996b <copy_file_contents+0xdb>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    98b8:	4c 89 ef             	mov    %r13,%rdi
    98bb:	49 89 c4             	mov    %rax,%r12
    98be:	31 f6                	xor    %esi,%esi
    98c0:	31 c0                	xor    %eax,%eax
    98c2:	e8 59 af ff ff       	call   4820 <open@plt>
    98c7:	41 89 c5             	mov    %eax,%r13d
    if (fd < 0)
    98ca:	85 c0                	test   %eax,%eax
    98cc:	0f 88 89 af ff ff    	js     485b <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    98d2:	48 89 ea             	mov    %rbp,%rdx
    98d5:	4c 89 e6             	mov    %r12,%rsi
    98d8:	89 c7                	mov    %eax,%edi
    98da:	e8 21 ad ff ff       	call   4600 <read@plt>
    if (ret < file_size) {
    98df:	48 98                	cltq
    98e1:	48 39 e8             	cmp    %rbp,%rax
    98e4:	7c 42                	jl     9928 <copy_file_contents+0x98>
    close(fd);
    98e6:	44 89 ef             	mov    %r13d,%edi
    98e9:	e8 a2 ab ff ff       	call   4490 <close@plt>
    iov->iov_base = buf;
    98ee:	48 89 d8             	mov    %rbx,%rax
    98f1:	48 c1 e8 03          	shr    $0x3,%rax
    98f5:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    98fc:	75 65                	jne    9963 <copy_file_contents+0xd3>
    iov->iov_len = file_size;
    98fe:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    iov->iov_base = buf;
    9902:	4c 89 23             	mov    %r12,(%rbx)
    iov->iov_len = file_size;
    9905:	48 89 f8             	mov    %rdi,%rax
    9908:	48 c1 e8 03          	shr    $0x3,%rax
    990c:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    9913:	75 49                	jne    995e <copy_file_contents+0xce>
    9915:	48 89 6b 08          	mov    %rbp,0x8(%rbx)
}
    9919:	48 83 c4 08          	add    $0x8,%rsp
    991d:	5b                   	pop    %rbx
    991e:	5d                   	pop    %rbp
    991f:	41 5c                	pop    %r12
    9921:	41 5d                	pop    %r13
    9923:	c3                   	ret
    9924:	0f 1f 40 00          	nopl   0x0(%rax)
        fprintf(stderr, "Encountered a short read.\n");
    9928:	48 8d 3d 71 c2 00 00 	lea    0xc271(%rip),%rdi        # 15ba0 <stderr@GLIBC_2.2.5>
    992f:	48 89 f8             	mov    %rdi,%rax
    9932:	48 c1 e8 03          	shr    $0x3,%rax
    9936:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    993d:	75 6f                	jne    99ae <copy_file_contents+0x11e>
    993f:	48 8b 0d 5a c2 00 00 	mov    0xc25a(%rip),%rcx        # 15ba0 <stderr@GLIBC_2.2.5>
    9946:	ba 1a 00 00 00       	mov    $0x1a,%edx
    994b:	be 01 00 00 00       	mov    $0x1,%esi
    9950:	48 8d 3d 09 6f 00 00 	lea    0x6f09(%rip),%rdi        # 10860 <_IO_stdin_used+0x860>
    9957:	e8 44 ab ff ff       	call   44a0 <fwrite@plt>
    995c:	eb 88                	jmp    98e6 <copy_file_contents+0x56>
    iov->iov_len = file_size;
    995e:	e8 6d ad ff ff       	call   46d0 <__asan_report_store8@plt>
    iov->iov_base = buf;
    9963:	48 89 df             	mov    %rbx,%rdi
    9966:	e8 65 ad ff ff       	call   46d0 <__asan_report_store8@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    996b:	48 8d 3d 2e c2 00 00 	lea    0xc22e(%rip),%rdi        # 15ba0 <stderr@GLIBC_2.2.5>
    9972:	48 89 f8             	mov    %rdi,%rax
    9975:	48 c1 e8 03          	shr    $0x3,%rax
    9979:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    9980:	75 31                	jne    99b3 <copy_file_contents+0x123>
    9982:	48 8b 0d 17 c2 00 00 	mov    0xc217(%rip),%rcx        # 15ba0 <stderr@GLIBC_2.2.5>
    9989:	ba 28 00 00 00       	mov    $0x28,%edx
    998e:	be 01 00 00 00       	mov    $0x1,%esi
    9993:	48 8d 3d c6 68 00 00 	lea    0x68c6(%rip),%rdi        # 10260 <_IO_stdin_used+0x260>
    999a:	e8 01 ab ff ff       	call   44a0 <fwrite@plt>
        exit(1);
    999f:	e8 6c ac ff ff       	call   4610 <__asan_handle_no_return@plt>
    99a4:	bf 01 00 00 00       	mov    $0x1,%edi
    99a9:	e8 62 ab ff ff       	call   4510 <exit@plt>
        fprintf(stderr, "Encountered a short read.\n");
    99ae:	e8 2d ab ff ff       	call   44e0 <__asan_report_load8@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    99b3:	e8 28 ab ff ff       	call   44e0 <__asan_report_load8@plt>
    99b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

00000000000099c0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    99c0:	f3 0f 1e fa          	endbr64
    99c4:	48 89 fa             	mov    %rdi,%rdx
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    99c7:	48 8d 7e 44          	lea    0x44(%rsi),%rdi
    99cb:	48 83 ec 08          	sub    $0x8,%rsp
    99cf:	48 89 f0             	mov    %rsi,%rax
    99d2:	48 89 f9             	mov    %rdi,%rcx
    99d5:	48 c1 e9 03          	shr    $0x3,%rcx
    99d9:	0f b6 b1 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%esi
    99e0:	48 89 f9             	mov    %rdi,%rcx
    99e3:	83 e1 07             	and    $0x7,%ecx
    99e6:	83 c1 03             	add    $0x3,%ecx
    99e9:	40 38 f1             	cmp    %sil,%cl
    99ec:	7c 09                	jl     99f7 <add_write_request+0x37>
    99ee:	40 84 f6             	test   %sil,%sil
    99f1:	0f 85 ee 03 00 00    	jne    9de5 <add_write_request+0x425>
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    99f7:	48 8d b8 c0 00 00 00 	lea    0xc0(%rax),%rdi
	unsigned int head, next = sq->sqe_tail + 1;
    99fe:	8b 70 44             	mov    0x44(%rax),%esi
	if (ring->flags & IORING_SETUP_SQE128)
    9a01:	48 89 f9             	mov    %rdi,%rcx
    9a04:	48 c1 e9 03          	shr    $0x3,%rcx
	unsigned int head, next = sq->sqe_tail + 1;
    9a08:	83 c6 01             	add    $0x1,%esi
	if (ring->flags & IORING_SETUP_SQE128)
    9a0b:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    9a12:	84 c9                	test   %cl,%cl
    9a14:	74 09                	je     9a1f <add_write_request+0x5f>
    9a16:	80 f9 03             	cmp    $0x3,%cl
    9a19:	0f 8e c1 03 00 00    	jle    9de0 <add_write_request+0x420>
    9a1f:	8b 88 c0 00 00 00    	mov    0xc0(%rax),%ecx
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    9a25:	48 89 c7             	mov    %rax,%rdi
    9a28:	48 c1 ef 03          	shr    $0x3,%rdi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    9a2c:	41 89 c8             	mov    %ecx,%r8d
    9a2f:	41 83 e0 02          	and    $0x2,%r8d
		head = IO_URING_READ_ONCE(*sq->khead);
    9a33:	80 bf 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdi)
    9a3a:	0f 85 19 04 00 00    	jne    9e59 <add_write_request+0x499>
    9a40:	48 8b 38             	mov    (%rax),%rdi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    9a43:	45 85 c0             	test   %r8d,%r8d
		head = IO_URING_READ_ONCE(*sq->khead);
    9a46:	49 89 f8             	mov    %rdi,%r8
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    9a49:	0f 85 61 03 00 00    	jne    9db0 <add_write_request+0x3f0>
		head = IO_URING_READ_ONCE(*sq->khead);
    9a4f:	49 c1 e8 03          	shr    $0x3,%r8
    9a53:	45 0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%r8),%r9d
    9a5b:	49 89 f8             	mov    %rdi,%r8
    9a5e:	41 83 e0 07          	and    $0x7,%r8d
    9a62:	41 83 c0 03          	add    $0x3,%r8d
    9a66:	45 38 c8             	cmp    %r9b,%r8b
    9a69:	7c 09                	jl     9a74 <add_write_request+0xb4>
    9a6b:	45 84 c9             	test   %r9b,%r9b
    9a6e:	0f 85 e0 03 00 00    	jne    9e54 <add_write_request+0x494>
    9a74:	8b 3f                	mov    (%rdi),%edi
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    9a76:	4c 8d 40 5c          	lea    0x5c(%rax),%r8
    9a7a:	41 89 f2             	mov    %esi,%r10d
    9a7d:	41 29 fa             	sub    %edi,%r10d
    9a80:	4c 89 c7             	mov    %r8,%rdi
    9a83:	48 c1 ef 03          	shr    $0x3,%rdi
    9a87:	44 0f b6 8f 00 80 ff 7f 	movzbl 0x7fff8000(%rdi),%r9d
    9a8f:	4c 89 c7             	mov    %r8,%rdi
    9a92:	83 e7 07             	and    $0x7,%edi
    9a95:	83 c7 03             	add    $0x3,%edi
    9a98:	44 38 cf             	cmp    %r9b,%dil
    9a9b:	7c 09                	jl     9aa6 <add_write_request+0xe6>
    9a9d:	45 84 c9             	test   %r9b,%r9b
    9aa0:	0f 85 32 03 00 00    	jne    9dd8 <add_write_request+0x418>
    9aa6:	44 39 50 5c          	cmp    %r10d,0x5c(%rax)
    9aaa:	0f 82 bc ad ff ff    	jb     486c <add_write_request.cold>
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    9ab0:	48 8d 78 38          	lea    0x38(%rax),%rdi
    9ab4:	49 89 f8             	mov    %rdi,%r8
    9ab7:	49 c1 e8 03          	shr    $0x3,%r8
    9abb:	41 80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r8)
    9ac3:	0f 85 a0 03 00 00    	jne    9e69 <add_write_request+0x4a9>
    9ac9:	4c 8d 50 58          	lea    0x58(%rax),%r10
    9acd:	48 8b 78 38          	mov    0x38(%rax),%rdi
    9ad1:	44 8b 40 44          	mov    0x44(%rax),%r8d
    9ad5:	4d 89 d1             	mov    %r10,%r9
    9ad8:	49 c1 e9 03          	shr    $0x3,%r9
    9adc:	45 0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%r9),%r9d
    9ae4:	45 84 c9             	test   %r9b,%r9b
    9ae7:	74 0a                	je     9af3 <add_write_request+0x133>
    9ae9:	41 80 f9 03          	cmp    $0x3,%r9b
    9aed:	0f 8e ff 02 00 00    	jle    9df2 <add_write_request+0x432>
	if (ring->flags & IORING_SETUP_SQE128)
    9af3:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    9af6:	44 23 40 58          	and    0x58(%rax),%r8d
		sq->sqe_tail = next;
    9afa:	89 70 44             	mov    %esi,0x44(%rax)
	if (ring->flags & IORING_SETUP_SQE128)
    9afd:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    9b00:	41 d3 e0             	shl    %cl,%r8d
    req->event_type = EVENT_TYPE_WRITE;
    9b03:	48 89 d1             	mov    %rdx,%rcx
    9b06:	48 c1 e9 03          	shr    $0x3,%rcx
    9b0a:	49 c1 e0 06          	shl    $0x6,%r8
    9b0e:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    9b15:	4c 01 c7             	add    %r8,%rdi
    9b18:	84 c9                	test   %cl,%cl
    9b1a:	74 09                	je     9b25 <add_write_request+0x165>
    9b1c:	80 f9 03             	cmp    $0x3,%cl
    9b1f:	0f 8e c5 02 00 00    	jle    9dea <add_write_request+0x42a>
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    9b25:	48 8d 72 04          	lea    0x4(%rdx),%rsi
    req->event_type = EVENT_TYPE_WRITE;
    9b29:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    9b2f:	48 89 f1             	mov    %rsi,%rcx
    9b32:	48 c1 e9 03          	shr    $0x3,%rcx
    9b36:	44 0f b6 81 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%r8d
    9b3e:	48 89 f1             	mov    %rsi,%rcx
    9b41:	83 e1 07             	and    $0x7,%ecx
    9b44:	83 c1 03             	add    $0x3,%ecx
    9b47:	44 38 c1             	cmp    %r8b,%cl
    9b4a:	7c 09                	jl     9b55 <add_write_request+0x195>
    9b4c:	45 84 c0             	test   %r8b,%r8b
    9b4f:	0f 85 ba 02 00 00    	jne    9e0f <add_write_request+0x44f>
    9b55:	48 8d 72 08          	lea    0x8(%rdx),%rsi
    9b59:	44 8b 4a 04          	mov    0x4(%rdx),%r9d
    9b5d:	4c 8d 52 10          	lea    0x10(%rdx),%r10
    9b61:	48 89 f1             	mov    %rsi,%rcx
    9b64:	48 c1 e9 03          	shr    $0x3,%rcx
    9b68:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    9b6f:	84 c9                	test   %cl,%cl
    9b71:	74 09                	je     9b7c <add_write_request+0x1bc>
    9b73:	80 f9 03             	cmp    $0x3,%cl
    9b76:	0f 8e 8b 02 00 00    	jle    9e07 <add_write_request+0x447>
	sqe->opcode = (__u8) op;
    9b7c:	48 89 f9             	mov    %rdi,%rcx
    9b7f:	44 8b 5a 08          	mov    0x8(%rdx),%r11d
    9b83:	48 c1 e9 03          	shr    $0x3,%rcx
    9b87:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    9b8e:	84 c9                	test   %cl,%cl
    9b90:	74 06                	je     9b98 <add_write_request+0x1d8>
    9b92:	0f 8e 6a 02 00 00    	jle    9e02 <add_write_request+0x442>
	sqe->flags = 0;
    9b98:	48 8d 4f 01          	lea    0x1(%rdi),%rcx
	sqe->opcode = (__u8) op;
    9b9c:	c6 07 02             	movb   $0x2,(%rdi)
	sqe->flags = 0;
    9b9f:	48 89 ce             	mov    %rcx,%rsi
    9ba2:	49 89 c8             	mov    %rcx,%r8
    9ba5:	48 c1 ee 03          	shr    $0x3,%rsi
    9ba9:	41 83 e0 07          	and    $0x7,%r8d
    9bad:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    9bb4:	44 38 c6             	cmp    %r8b,%sil
    9bb7:	7f 09                	jg     9bc2 <add_write_request+0x202>
    9bb9:	40 84 f6             	test   %sil,%sil
    9bbc:	0f 85 38 02 00 00    	jne    9dfa <add_write_request+0x43a>
	sqe->ioprio = 0;
    9bc2:	48 8d 77 02          	lea    0x2(%rdi),%rsi
	sqe->flags = 0;
    9bc6:	c6 47 01 00          	movb   $0x0,0x1(%rdi)
	sqe->ioprio = 0;
    9bca:	48 89 f1             	mov    %rsi,%rcx
    9bcd:	48 c1 e9 03          	shr    $0x3,%rcx
    9bd1:	44 0f b6 81 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%r8d
    9bd9:	48 89 f1             	mov    %rsi,%rcx
    9bdc:	83 e1 07             	and    $0x7,%ecx
    9bdf:	83 c1 01             	add    $0x1,%ecx
    9be2:	44 38 c1             	cmp    %r8b,%cl
    9be5:	7c 09                	jl     9bf0 <add_write_request+0x230>
    9be7:	45 84 c0             	test   %r8b,%r8b
    9bea:	0f 85 57 02 00 00    	jne    9e47 <add_write_request+0x487>
	sqe->fd = fd;
    9bf0:	48 8d 77 04          	lea    0x4(%rdi),%rsi
	sqe->ioprio = 0;
    9bf4:	45 31 c0             	xor    %r8d,%r8d
	sqe->fd = fd;
    9bf7:	48 89 f1             	mov    %rsi,%rcx
	sqe->ioprio = 0;
    9bfa:	66 44 89 47 02       	mov    %r8w,0x2(%rdi)
	sqe->fd = fd;
    9bff:	48 c1 e9 03          	shr    $0x3,%rcx
    9c03:	44 0f b6 81 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%r8d
    9c0b:	48 89 f1             	mov    %rsi,%rcx
    9c0e:	83 e1 07             	and    $0x7,%ecx
    9c11:	83 c1 03             	add    $0x3,%ecx
    9c14:	44 38 c1             	cmp    %r8b,%cl
    9c17:	7c 09                	jl     9c22 <add_write_request+0x262>
    9c19:	45 84 c0             	test   %r8b,%r8b
    9c1c:	0f 85 1d 02 00 00    	jne    9e3f <add_write_request+0x47f>
	sqe->off = offset;
    9c22:	48 8d 4f 08          	lea    0x8(%rdi),%rcx
	sqe->fd = fd;
    9c26:	44 89 5f 04          	mov    %r11d,0x4(%rdi)
	sqe->off = offset;
    9c2a:	48 89 ce             	mov    %rcx,%rsi
    9c2d:	48 c1 ee 03          	shr    $0x3,%rsi
    9c31:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    9c38:	0f 85 23 02 00 00    	jne    9e61 <add_write_request+0x4a1>
	sqe->addr = (unsigned long) addr;
    9c3e:	48 8d 4f 10          	lea    0x10(%rdi),%rcx
	sqe->off = offset;
    9c42:	48 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%rdi)
	sqe->addr = (unsigned long) addr;
    9c4a:	48 89 ce             	mov    %rcx,%rsi
    9c4d:	48 c1 ee 03          	shr    $0x3,%rsi
    9c51:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    9c58:	0f 85 28 02 00 00    	jne    9e86 <add_write_request+0x4c6>
	sqe->len = len;
    9c5e:	48 8d 77 18          	lea    0x18(%rdi),%rsi
	sqe->addr = (unsigned long) addr;
    9c62:	4c 89 57 10          	mov    %r10,0x10(%rdi)
	sqe->len = len;
    9c66:	48 89 f1             	mov    %rsi,%rcx
    9c69:	48 c1 e9 03          	shr    $0x3,%rcx
    9c6d:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    9c74:	84 c9                	test   %cl,%cl
    9c76:	74 09                	je     9c81 <add_write_request+0x2c1>
    9c78:	80 f9 03             	cmp    $0x3,%cl
    9c7b:	0f 8e b6 01 00 00    	jle    9e37 <add_write_request+0x477>
	sqe->rw_flags = 0;
    9c81:	48 8d 77 1c          	lea    0x1c(%rdi),%rsi
	sqe->len = len;
    9c85:	44 89 4f 18          	mov    %r9d,0x18(%rdi)
	sqe->rw_flags = 0;
    9c89:	48 89 f1             	mov    %rsi,%rcx
    9c8c:	48 c1 e9 03          	shr    $0x3,%rcx
    9c90:	44 0f b6 81 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%r8d
    9c98:	48 89 f1             	mov    %rsi,%rcx
    9c9b:	83 e1 07             	and    $0x7,%ecx
    9c9e:	83 c1 03             	add    $0x3,%ecx
    9ca1:	44 38 c1             	cmp    %r8b,%cl
    9ca4:	7c 09                	jl     9caf <add_write_request+0x2ef>
    9ca6:	45 84 c0             	test   %r8b,%r8b
    9ca9:	0f 85 80 01 00 00    	jne    9e2f <add_write_request+0x46f>
	sqe->buf_index = 0;
    9caf:	48 8d 77 28          	lea    0x28(%rdi),%rsi
	sqe->rw_flags = 0;
    9cb3:	c7 47 1c 00 00 00 00 	movl   $0x0,0x1c(%rdi)
	sqe->buf_index = 0;
    9cba:	48 89 f1             	mov    %rsi,%rcx
    9cbd:	48 c1 e9 03          	shr    $0x3,%rcx
    9cc1:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    9cc8:	84 c9                	test   %cl,%cl
    9cca:	74 09                	je     9cd5 <add_write_request+0x315>
    9ccc:	80 f9 01             	cmp    $0x1,%cl
    9ccf:	0f 8e 52 01 00 00    	jle    9e27 <add_write_request+0x467>
    9cd5:	31 f6                	xor    %esi,%esi
    9cd7:	66 89 77 28          	mov    %si,0x28(%rdi)
	sqe->personality = 0;
    9cdb:	48 8d 77 2a          	lea    0x2a(%rdi),%rsi
    9cdf:	48 89 f1             	mov    %rsi,%rcx
    9ce2:	48 c1 e9 03          	shr    $0x3,%rcx
    9ce6:	44 0f b6 81 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%r8d
    9cee:	48 89 f1             	mov    %rsi,%rcx
    9cf1:	83 e1 07             	and    $0x7,%ecx
    9cf4:	83 c1 01             	add    $0x1,%ecx
    9cf7:	44 38 c1             	cmp    %r8b,%cl
    9cfa:	7c 09                	jl     9d05 <add_write_request+0x345>
    9cfc:	45 84 c0             	test   %r8b,%r8b
    9cff:	0f 85 1a 01 00 00    	jne    9e1f <add_write_request+0x45f>
    9d05:	31 c9                	xor    %ecx,%ecx
	sqe->file_index = 0;
    9d07:	48 8d 77 2c          	lea    0x2c(%rdi),%rsi
	sqe->personality = 0;
    9d0b:	66 89 4f 2a          	mov    %cx,0x2a(%rdi)
	sqe->file_index = 0;
    9d0f:	48 89 f1             	mov    %rsi,%rcx
    9d12:	48 c1 e9 03          	shr    $0x3,%rcx
    9d16:	44 0f b6 81 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%r8d
    9d1e:	48 89 f1             	mov    %rsi,%rcx
    9d21:	83 e1 07             	and    $0x7,%ecx
    9d24:	83 c1 03             	add    $0x3,%ecx
    9d27:	44 38 c1             	cmp    %r8b,%cl
    9d2a:	7c 09                	jl     9d35 <add_write_request+0x375>
    9d2c:	45 84 c0             	test   %r8b,%r8b
    9d2f:	0f 85 e2 00 00 00    	jne    9e17 <add_write_request+0x457>
	sqe->addr3 = 0;
    9d35:	48 8d 4f 30          	lea    0x30(%rdi),%rcx
	sqe->file_index = 0;
    9d39:	c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%rdi)
	sqe->addr3 = 0;
    9d40:	48 89 ce             	mov    %rcx,%rsi
    9d43:	48 c1 ee 03          	shr    $0x3,%rsi
    9d47:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    9d4e:	0f 85 22 01 00 00    	jne    9e76 <add_write_request+0x4b6>
	sqe->__pad2[0] = 0;
    9d54:	48 8d 4f 38          	lea    0x38(%rdi),%rcx
	sqe->addr3 = 0;
    9d58:	48 c7 47 30 00 00 00 00 	movq   $0x0,0x30(%rdi)
	sqe->__pad2[0] = 0;
    9d60:	48 89 ce             	mov    %rcx,%rsi
    9d63:	48 c1 ee 03          	shr    $0x3,%rsi
    9d67:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    9d6e:	0f 85 fa 00 00 00    	jne    9e6e <add_write_request+0x4ae>
	sqe->user_data = (unsigned long) data;
    9d74:	48 8d 4f 20          	lea    0x20(%rdi),%rcx
	sqe->__pad2[0] = 0;
    9d78:	48 c7 47 38 00 00 00 00 	movq   $0x0,0x38(%rdi)
	sqe->user_data = (unsigned long) data;
    9d80:	48 89 ce             	mov    %rcx,%rsi
    9d83:	48 c1 ee 03          	shr    $0x3,%rsi
    9d87:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    9d8e:	0f 85 ea 00 00 00    	jne    9e7e <add_write_request+0x4be>
    9d94:	48 89 57 20          	mov    %rdx,0x20(%rdi)
    io_uring_submit(ring);
    9d98:	48 89 c7             	mov    %rax,%rdi
    9d9b:	e8 c0 a8 ff ff       	call   4660 <io_uring_submit@plt>
}
    9da0:	31 c0                	xor    %eax,%eax
    9da2:	48 83 c4 08          	add    $0x8,%rsp
    9da6:	c3                   	ret
    9da7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    9db0:	49 c1 e8 03          	shr    $0x3,%r8
    9db4:	45 0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%r8),%r9d
    9dbc:	49 89 f8             	mov    %rdi,%r8
    9dbf:	41 83 e0 07          	and    $0x7,%r8d
    9dc3:	41 83 c0 03          	add    $0x3,%r8d
    9dc7:	45 38 c8             	cmp    %r9b,%r8b
    9dca:	7c 05                	jl     9dd1 <add_write_request+0x411>
    9dcc:	45 84 c9             	test   %r9b,%r9b
    9dcf:	75 7e                	jne    9e4f <add_write_request+0x48f>
    9dd1:	8b 3f                	mov    (%rdi),%edi
    9dd3:	e9 9e fc ff ff       	jmp    9a76 <add_write_request+0xb6>
	if (next - head <= sq->ring_entries) {
    9dd8:	4c 89 c7             	mov    %r8,%rdi
    9ddb:	e8 70 a7 ff ff       	call   4550 <__asan_report_load4@plt>
	if (ring->flags & IORING_SETUP_SQE128)
    9de0:	e8 6b a7 ff ff       	call   4550 <__asan_report_load4@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    9de5:	e8 66 a7 ff ff       	call   4550 <__asan_report_load4@plt>
    req->event_type = EVENT_TYPE_WRITE;
    9dea:	48 89 d7             	mov    %rdx,%rdi
    9ded:	e8 ce a8 ff ff       	call   46c0 <__asan_report_store4@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    9df2:	4c 89 d7             	mov    %r10,%rdi
    9df5:	e8 56 a7 ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->flags = 0;
    9dfa:	48 89 cf             	mov    %rcx,%rdi
    9dfd:	e8 ce a9 ff ff       	call   47d0 <__asan_report_store1@plt>
	sqe->opcode = (__u8) op;
    9e02:	e8 c9 a9 ff ff       	call   47d0 <__asan_report_store1@plt>
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    9e07:	48 89 f7             	mov    %rsi,%rdi
    9e0a:	e8 41 a7 ff ff       	call   4550 <__asan_report_load4@plt>
    9e0f:	48 89 f7             	mov    %rsi,%rdi
    9e12:	e8 39 a7 ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->file_index = 0;
    9e17:	48 89 f7             	mov    %rsi,%rdi
    9e1a:	e8 a1 a8 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->personality = 0;
    9e1f:	48 89 f7             	mov    %rsi,%rdi
    9e22:	e8 d9 a6 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->buf_index = 0;
    9e27:	48 89 f7             	mov    %rsi,%rdi
    9e2a:	e8 d1 a6 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->rw_flags = 0;
    9e2f:	48 89 f7             	mov    %rsi,%rdi
    9e32:	e8 89 a8 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->len = len;
    9e37:	48 89 f7             	mov    %rsi,%rdi
    9e3a:	e8 81 a8 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->fd = fd;
    9e3f:	48 89 f7             	mov    %rsi,%rdi
    9e42:	e8 79 a8 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->ioprio = 0;
    9e47:	48 89 f7             	mov    %rsi,%rdi
    9e4a:	e8 b1 a6 ff ff       	call   4500 <__asan_report_store2@plt>
		head = io_uring_smp_load_acquire(sq->khead);
    9e4f:	e8 fc a6 ff ff       	call   4550 <__asan_report_load4@plt>
		head = IO_URING_READ_ONCE(*sq->khead);
    9e54:	e8 f7 a6 ff ff       	call   4550 <__asan_report_load4@plt>
    9e59:	48 89 c7             	mov    %rax,%rdi
    9e5c:	e8 7f a6 ff ff       	call   44e0 <__asan_report_load8@plt>
	sqe->off = offset;
    9e61:	48 89 cf             	mov    %rcx,%rdi
    9e64:	e8 67 a8 ff ff       	call   46d0 <__asan_report_store8@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    9e69:	e8 72 a6 ff ff       	call   44e0 <__asan_report_load8@plt>
	sqe->__pad2[0] = 0;
    9e6e:	48 89 cf             	mov    %rcx,%rdi
    9e71:	e8 5a a8 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->addr3 = 0;
    9e76:	48 89 cf             	mov    %rcx,%rdi
    9e79:	e8 52 a8 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->user_data = (unsigned long) data;
    9e7e:	48 89 cf             	mov    %rcx,%rdi
    9e81:	e8 4a a8 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->addr = (unsigned long) addr;
    9e86:	48 89 cf             	mov    %rcx,%rdi
    9e89:	e8 42 a8 ff ff       	call   46d0 <__asan_report_store8@plt>
    9e8e:	66 90                	xchg   %ax,%ax

0000000000009e90 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    9e90:	f3 0f 1e fa          	endbr64
    9e94:	41 55                	push   %r13
    9e96:	41 89 fd             	mov    %edi,%r13d
	unsigned int head, next = sq->sqe_tail + 1;
    9e99:	48 8d 7e 44          	lea    0x44(%rsi),%rdi
    9e9d:	41 54                	push   %r12
    9e9f:	48 89 f8             	mov    %rdi,%rax
    9ea2:	55                   	push   %rbp
    9ea3:	48 c1 e8 03          	shr    $0x3,%rax
    9ea7:	48 89 f5             	mov    %rsi,%rbp
    9eaa:	53                   	push   %rbx
    9eab:	48 83 ec 08          	sub    $0x8,%rsp
    9eaf:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    9eb6:	48 89 f8             	mov    %rdi,%rax
    9eb9:	83 e0 07             	and    $0x7,%eax
    9ebc:	83 c0 03             	add    $0x3,%eax
    9ebf:	38 d0                	cmp    %dl,%al
    9ec1:	7c 08                	jl     9ecb <add_read_request+0x3b>
    9ec3:	84 d2                	test   %dl,%dl
    9ec5:	0f 85 f4 03 00 00    	jne    a2bf <add_read_request+0x42f>
	if (ring->flags & IORING_SETUP_SQE128)
    9ecb:	48 8d bd c0 00 00 00 	lea    0xc0(%rbp),%rdi
	unsigned int head, next = sq->sqe_tail + 1;
    9ed2:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    9ed5:	48 89 fa             	mov    %rdi,%rdx
    9ed8:	48 c1 ea 03          	shr    $0x3,%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    9edc:	83 c0 01             	add    $0x1,%eax
	if (ring->flags & IORING_SETUP_SQE128)
    9edf:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    9ee6:	84 d2                	test   %dl,%dl
    9ee8:	74 09                	je     9ef3 <add_read_request+0x63>
    9eea:	80 fa 03             	cmp    $0x3,%dl
    9eed:	0f 8e c7 03 00 00    	jle    a2ba <add_read_request+0x42a>
    9ef3:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    9ef9:	48 89 ee             	mov    %rbp,%rsi
    9efc:	48 c1 ee 03          	shr    $0x3,%rsi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    9f00:	89 ca                	mov    %ecx,%edx
    9f02:	83 e2 02             	and    $0x2,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    9f05:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    9f0c:	0f 85 0a 04 00 00    	jne    a31c <add_read_request+0x48c>
    9f12:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    9f16:	85 d2                	test   %edx,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    9f18:	48 89 fa             	mov    %rdi,%rdx
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    9f1b:	0f 85 6f 03 00 00    	jne    a290 <add_read_request+0x400>
		head = IO_URING_READ_ONCE(*sq->khead);
    9f21:	48 c1 ea 03          	shr    $0x3,%rdx
    9f25:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    9f2c:	48 89 fa             	mov    %rdi,%rdx
    9f2f:	83 e2 07             	and    $0x7,%edx
    9f32:	83 c2 03             	add    $0x3,%edx
    9f35:	40 38 f2             	cmp    %sil,%dl
    9f38:	7c 09                	jl     9f43 <add_read_request+0xb3>
    9f3a:	40 84 f6             	test   %sil,%sil
    9f3d:	0f 85 cf 03 00 00    	jne    a312 <add_read_request+0x482>
    9f43:	8b 17                	mov    (%rdi),%edx
	if (next - head <= sq->ring_entries) {
    9f45:	48 8d 7d 5c          	lea    0x5c(%rbp),%rdi
    9f49:	41 89 c0             	mov    %eax,%r8d
    9f4c:	41 29 d0             	sub    %edx,%r8d
    9f4f:	48 89 fa             	mov    %rdi,%rdx
    9f52:	48 c1 ea 03          	shr    $0x3,%rdx
    9f56:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    9f5d:	48 89 fa             	mov    %rdi,%rdx
    9f60:	83 e2 07             	and    $0x7,%edx
    9f63:	83 c2 03             	add    $0x3,%edx
    9f66:	40 38 f2             	cmp    %sil,%dl
    9f69:	7c 09                	jl     9f74 <add_read_request+0xe4>
    9f6b:	40 84 f6             	test   %sil,%sil
    9f6e:	0f 85 41 03 00 00    	jne    a2b5 <add_read_request+0x425>
    9f74:	44 39 45 5c          	cmp    %r8d,0x5c(%rbp)
    9f78:	0f 82 31 a9 ff ff    	jb     48af <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    9f7e:	48 8d 7d 38          	lea    0x38(%rbp),%rdi
    9f82:	48 89 fa             	mov    %rdi,%rdx
    9f85:	48 c1 ea 03          	shr    $0x3,%rdx
    9f89:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    9f90:	0f 85 8e 03 00 00    	jne    a324 <add_read_request+0x494>
    9f96:	48 8d 7d 58          	lea    0x58(%rbp),%rdi
    9f9a:	48 8b 5d 38          	mov    0x38(%rbp),%rbx
    9f9e:	8b 55 44             	mov    0x44(%rbp),%edx
    9fa1:	48 89 fe             	mov    %rdi,%rsi
    9fa4:	48 c1 ee 03          	shr    $0x3,%rsi
    9fa8:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    9faf:	40 84 f6             	test   %sil,%sil
    9fb2:	74 0a                	je     9fbe <add_read_request+0x12e>
    9fb4:	40 80 fe 03          	cmp    $0x3,%sil
    9fb8:	0f 8e 0e 03 00 00    	jle    a2cc <add_read_request+0x43c>
	if (ring->flags & IORING_SETUP_SQE128)
    9fbe:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    9fc1:	23 55 58             	and    0x58(%rbp),%edx
		sq->sqe_tail = next;
    9fc4:	89 45 44             	mov    %eax,0x44(%rbp)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    9fc7:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    9fcc:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    9fcf:	d3 e2                	shl    %cl,%edx
    9fd1:	48 c1 e2 06          	shl    $0x6,%rdx
    9fd5:	48 01 d3             	add    %rdx,%rbx
    9fd8:	e8 b3 a5 ff ff       	call   4590 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    9fdd:	bf 00 20 00 00       	mov    $0x2000,%edi
    9fe2:	be 01 00 00 00       	mov    $0x1,%esi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    9fe7:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    9fea:	e8 71 a4 ff ff       	call   4460 <calloc@plt>
    9fef:	49 8d 7c 24 10       	lea    0x10(%r12),%rdi
    9ff4:	48 89 fa             	mov    %rdi,%rdx
    9ff7:	48 c1 ea 03          	shr    $0x3,%rdx
    9ffb:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    a002:	0f 85 43 03 00 00    	jne    a34b <add_read_request+0x4bb>
    a008:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    req->iov[0].iov_len = READ_SZ;
    a00d:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    a012:	48 89 c2             	mov    %rax,%rdx
    a015:	48 c1 ea 03          	shr    $0x3,%rdx
    a019:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    a020:	0f 85 1d 03 00 00    	jne    a343 <add_read_request+0x4b3>
    a026:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    a02f:	4c 89 e0             	mov    %r12,%rax
    a032:	48 c1 e8 03          	shr    $0x3,%rax
    a036:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    a03d:	84 c0                	test   %al,%al
    a03f:	74 08                	je     a049 <add_read_request+0x1b9>
    a041:	3c 03                	cmp    $0x3,%al
    a043:	0f 8e 7b 02 00 00    	jle    a2c4 <add_read_request+0x434>
    req->client_socket = client_socket;
    a049:	49 8d 54 24 08       	lea    0x8(%r12),%rdx
    req->event_type = EVENT_TYPE_READ;
    a04e:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    req->client_socket = client_socket;
    a056:	48 89 d0             	mov    %rdx,%rax
    a059:	48 c1 e8 03          	shr    $0x3,%rax
    a05d:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    a064:	84 c0                	test   %al,%al
    a066:	74 08                	je     a070 <add_read_request+0x1e0>
    a068:	3c 03                	cmp    $0x3,%al
    a06a:	0f 8e 79 02 00 00    	jle    a2e9 <add_read_request+0x459>
	sqe->opcode = (__u8) op;
    a070:	48 89 d8             	mov    %rbx,%rax
    a073:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    a078:	48 c1 e8 03          	shr    $0x3,%rax
    a07c:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    a083:	84 c0                	test   %al,%al
    a085:	74 06                	je     a08d <add_read_request+0x1fd>
    a087:	0f 8e 54 02 00 00    	jle    a2e1 <add_read_request+0x451>
	sqe->flags = 0;
    a08d:	48 8d 43 01          	lea    0x1(%rbx),%rax
	sqe->opcode = (__u8) op;
    a091:	c6 03 01             	movb   $0x1,(%rbx)
	sqe->flags = 0;
    a094:	48 89 c2             	mov    %rax,%rdx
    a097:	48 89 c1             	mov    %rax,%rcx
    a09a:	48 c1 ea 03          	shr    $0x3,%rdx
    a09e:	83 e1 07             	and    $0x7,%ecx
    a0a1:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    a0a8:	38 ca                	cmp    %cl,%dl
    a0aa:	7f 08                	jg     a0b4 <add_read_request+0x224>
    a0ac:	84 d2                	test   %dl,%dl
    a0ae:	0f 85 25 02 00 00    	jne    a2d9 <add_read_request+0x449>
	sqe->ioprio = 0;
    a0b4:	48 8d 53 02          	lea    0x2(%rbx),%rdx
	sqe->flags = 0;
    a0b8:	c6 43 01 00          	movb   $0x0,0x1(%rbx)
	sqe->ioprio = 0;
    a0bc:	48 89 d0             	mov    %rdx,%rax
    a0bf:	48 c1 e8 03          	shr    $0x3,%rax
    a0c3:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    a0ca:	48 89 d0             	mov    %rdx,%rax
    a0cd:	83 e0 07             	and    $0x7,%eax
    a0d0:	83 c0 01             	add    $0x1,%eax
    a0d3:	38 c8                	cmp    %cl,%al
    a0d5:	7c 08                	jl     a0df <add_read_request+0x24f>
    a0d7:	84 c9                	test   %cl,%cl
    a0d9:	0f 85 f2 01 00 00    	jne    a2d1 <add_read_request+0x441>
	sqe->fd = fd;
    a0df:	48 8d 53 04          	lea    0x4(%rbx),%rdx
	sqe->ioprio = 0;
    a0e3:	31 c9                	xor    %ecx,%ecx
	sqe->fd = fd;
    a0e5:	48 89 d0             	mov    %rdx,%rax
	sqe->ioprio = 0;
    a0e8:	66 89 4b 02          	mov    %cx,0x2(%rbx)
	sqe->fd = fd;
    a0ec:	48 c1 e8 03          	shr    $0x3,%rax
    a0f0:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    a0f7:	48 89 d0             	mov    %rdx,%rax
    a0fa:	83 e0 07             	and    $0x7,%eax
    a0fd:	83 c0 03             	add    $0x3,%eax
    a100:	38 c8                	cmp    %cl,%al
    a102:	7c 08                	jl     a10c <add_read_request+0x27c>
    a104:	84 c9                	test   %cl,%cl
    a106:	0f 85 fe 01 00 00    	jne    a30a <add_read_request+0x47a>
	sqe->off = offset;
    a10c:	48 8d 43 08          	lea    0x8(%rbx),%rax
	sqe->fd = fd;
    a110:	44 89 6b 04          	mov    %r13d,0x4(%rbx)
	sqe->off = offset;
    a114:	48 89 c2             	mov    %rax,%rdx
    a117:	48 c1 ea 03          	shr    $0x3,%rdx
    a11b:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    a122:	0f 85 13 02 00 00    	jne    a33b <add_read_request+0x4ab>
	sqe->addr = (unsigned long) addr;
    a128:	48 8d 43 10          	lea    0x10(%rbx),%rax
	sqe->off = offset;
    a12c:	48 c7 43 08 00 00 00 00 	movq   $0x0,0x8(%rbx)
	sqe->addr = (unsigned long) addr;
    a134:	48 89 c2             	mov    %rax,%rdx
    a137:	48 c1 ea 03          	shr    $0x3,%rdx
    a13b:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    a142:	0f 85 e1 01 00 00    	jne    a329 <add_read_request+0x499>
    a148:	48 89 7b 10          	mov    %rdi,0x10(%rbx)
	sqe->len = len;
    a14c:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    a150:	48 89 f8             	mov    %rdi,%rax
    a153:	48 c1 e8 03          	shr    $0x3,%rax
    a157:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    a15e:	84 c0                	test   %al,%al
    a160:	74 08                	je     a16a <add_read_request+0x2da>
    a162:	3c 03                	cmp    $0x3,%al
    a164:	0f 8e 9b 01 00 00    	jle    a305 <add_read_request+0x475>
	sqe->rw_flags = 0;
    a16a:	48 8d 7b 1c          	lea    0x1c(%rbx),%rdi
	sqe->len = len;
    a16e:	c7 43 18 01 00 00 00 	movl   $0x1,0x18(%rbx)
	sqe->rw_flags = 0;
    a175:	48 89 f8             	mov    %rdi,%rax
    a178:	48 c1 e8 03          	shr    $0x3,%rax
    a17c:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    a183:	48 89 f8             	mov    %rdi,%rax
    a186:	83 e0 07             	and    $0x7,%eax
    a189:	83 c0 03             	add    $0x3,%eax
    a18c:	38 d0                	cmp    %dl,%al
    a18e:	7c 08                	jl     a198 <add_read_request+0x308>
    a190:	84 d2                	test   %dl,%dl
    a192:	0f 85 68 01 00 00    	jne    a300 <add_read_request+0x470>
	sqe->buf_index = 0;
    a198:	48 8d 7b 28          	lea    0x28(%rbx),%rdi
	sqe->rw_flags = 0;
    a19c:	c7 43 1c 00 00 00 00 	movl   $0x0,0x1c(%rbx)
	sqe->buf_index = 0;
    a1a3:	48 89 f8             	mov    %rdi,%rax
    a1a6:	48 c1 e8 03          	shr    $0x3,%rax
    a1aa:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    a1b1:	84 c0                	test   %al,%al
    a1b3:	74 08                	je     a1bd <add_read_request+0x32d>
    a1b5:	3c 01                	cmp    $0x1,%al
    a1b7:	0f 8e 3e 01 00 00    	jle    a2fb <add_read_request+0x46b>
	sqe->personality = 0;
    a1bd:	48 8d 7b 2a          	lea    0x2a(%rbx),%rdi
	sqe->buf_index = 0;
    a1c1:	31 d2                	xor    %edx,%edx
	sqe->personality = 0;
    a1c3:	48 89 f8             	mov    %rdi,%rax
	sqe->buf_index = 0;
    a1c6:	66 89 53 28          	mov    %dx,0x28(%rbx)
	sqe->personality = 0;
    a1ca:	48 c1 e8 03          	shr    $0x3,%rax
    a1ce:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    a1d5:	48 89 f8             	mov    %rdi,%rax
    a1d8:	83 e0 07             	and    $0x7,%eax
    a1db:	83 c0 01             	add    $0x1,%eax
    a1de:	38 d0                	cmp    %dl,%al
    a1e0:	7c 08                	jl     a1ea <add_read_request+0x35a>
    a1e2:	84 d2                	test   %dl,%dl
    a1e4:	0f 85 0c 01 00 00    	jne    a2f6 <add_read_request+0x466>
    a1ea:	31 c0                	xor    %eax,%eax
	sqe->file_index = 0;
    a1ec:	48 8d 7b 2c          	lea    0x2c(%rbx),%rdi
	sqe->personality = 0;
    a1f0:	66 89 43 2a          	mov    %ax,0x2a(%rbx)
	sqe->file_index = 0;
    a1f4:	48 89 f8             	mov    %rdi,%rax
    a1f7:	48 c1 e8 03          	shr    $0x3,%rax
    a1fb:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    a202:	48 89 f8             	mov    %rdi,%rax
    a205:	83 e0 07             	and    $0x7,%eax
    a208:	83 c0 03             	add    $0x3,%eax
    a20b:	38 d0                	cmp    %dl,%al
    a20d:	7c 08                	jl     a217 <add_read_request+0x387>
    a20f:	84 d2                	test   %dl,%dl
    a211:	0f 85 da 00 00 00    	jne    a2f1 <add_read_request+0x461>
	sqe->addr3 = 0;
    a217:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
	sqe->file_index = 0;
    a21b:	c7 43 2c 00 00 00 00 	movl   $0x0,0x2c(%rbx)
	sqe->addr3 = 0;
    a222:	48 89 f8             	mov    %rdi,%rax
    a225:	48 c1 e8 03          	shr    $0x3,%rax
    a229:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    a230:	0f 85 00 01 00 00    	jne    a336 <add_read_request+0x4a6>
	sqe->__pad2[0] = 0;
    a236:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
	sqe->addr3 = 0;
    a23a:	48 c7 43 30 00 00 00 00 	movq   $0x0,0x30(%rbx)
	sqe->__pad2[0] = 0;
    a242:	48 89 f8             	mov    %rdi,%rax
    a245:	48 c1 e8 03          	shr    $0x3,%rax
    a249:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    a250:	0f 85 db 00 00 00    	jne    a331 <add_read_request+0x4a1>
	sqe->user_data = (unsigned long) data;
    a256:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
	sqe->__pad2[0] = 0;
    a25a:	48 c7 43 38 00 00 00 00 	movq   $0x0,0x38(%rbx)
	sqe->user_data = (unsigned long) data;
    a262:	48 89 f8             	mov    %rdi,%rax
    a265:	48 c1 e8 03          	shr    $0x3,%rax
    a269:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    a270:	0f 85 da 00 00 00    	jne    a350 <add_read_request+0x4c0>
    a276:	4c 89 63 20          	mov    %r12,0x20(%rbx)
    io_uring_submit(ring);
    a27a:	48 89 ef             	mov    %rbp,%rdi
    a27d:	e8 de a3 ff ff       	call   4660 <io_uring_submit@plt>
}
    a282:	48 83 c4 08          	add    $0x8,%rsp
    a286:	31 c0                	xor    %eax,%eax
    a288:	5b                   	pop    %rbx
    a289:	5d                   	pop    %rbp
    a28a:	41 5c                	pop    %r12
    a28c:	41 5d                	pop    %r13
    a28e:	c3                   	ret
    a28f:	90                   	nop
		head = io_uring_smp_load_acquire(sq->khead);
    a290:	48 c1 ea 03          	shr    $0x3,%rdx
    a294:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    a29b:	48 89 fa             	mov    %rdi,%rdx
    a29e:	83 e2 07             	and    $0x7,%edx
    a2a1:	83 c2 03             	add    $0x3,%edx
    a2a4:	40 38 f2             	cmp    %sil,%dl
    a2a7:	7c 05                	jl     a2ae <add_read_request+0x41e>
    a2a9:	40 84 f6             	test   %sil,%sil
    a2ac:	75 69                	jne    a317 <add_read_request+0x487>
    a2ae:	8b 17                	mov    (%rdi),%edx
    a2b0:	e9 90 fc ff ff       	jmp    9f45 <add_read_request+0xb5>
	if (next - head <= sq->ring_entries) {
    a2b5:	e8 96 a2 ff ff       	call   4550 <__asan_report_load4@plt>
	if (ring->flags & IORING_SETUP_SQE128)
    a2ba:	e8 91 a2 ff ff       	call   4550 <__asan_report_load4@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    a2bf:	e8 8c a2 ff ff       	call   4550 <__asan_report_load4@plt>
    req->event_type = EVENT_TYPE_READ;
    a2c4:	4c 89 e7             	mov    %r12,%rdi
    a2c7:	e8 f4 a3 ff ff       	call   46c0 <__asan_report_store4@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    a2cc:	e8 7f a2 ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->ioprio = 0;
    a2d1:	48 89 d7             	mov    %rdx,%rdi
    a2d4:	e8 27 a2 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->flags = 0;
    a2d9:	48 89 c7             	mov    %rax,%rdi
    a2dc:	e8 ef a4 ff ff       	call   47d0 <__asan_report_store1@plt>
	sqe->opcode = (__u8) op;
    a2e1:	48 89 df             	mov    %rbx,%rdi
    a2e4:	e8 e7 a4 ff ff       	call   47d0 <__asan_report_store1@plt>
    req->client_socket = client_socket;
    a2e9:	48 89 d7             	mov    %rdx,%rdi
    a2ec:	e8 cf a3 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->file_index = 0;
    a2f1:	e8 ca a3 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->personality = 0;
    a2f6:	e8 05 a2 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->buf_index = 0;
    a2fb:	e8 00 a2 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->rw_flags = 0;
    a300:	e8 bb a3 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->len = len;
    a305:	e8 b6 a3 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->fd = fd;
    a30a:	48 89 d7             	mov    %rdx,%rdi
    a30d:	e8 ae a3 ff ff       	call   46c0 <__asan_report_store4@plt>
		head = IO_URING_READ_ONCE(*sq->khead);
    a312:	e8 39 a2 ff ff       	call   4550 <__asan_report_load4@plt>
		head = io_uring_smp_load_acquire(sq->khead);
    a317:	e8 34 a2 ff ff       	call   4550 <__asan_report_load4@plt>
		head = IO_URING_READ_ONCE(*sq->khead);
    a31c:	48 89 ef             	mov    %rbp,%rdi
    a31f:	e8 bc a1 ff ff       	call   44e0 <__asan_report_load8@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    a324:	e8 b7 a1 ff ff       	call   44e0 <__asan_report_load8@plt>
	sqe->addr = (unsigned long) addr;
    a329:	48 89 c7             	mov    %rax,%rdi
    a32c:	e8 9f a3 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->__pad2[0] = 0;
    a331:	e8 9a a3 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->addr3 = 0;
    a336:	e8 95 a3 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->off = offset;
    a33b:	48 89 c7             	mov    %rax,%rdi
    a33e:	e8 8d a3 ff ff       	call   46d0 <__asan_report_store8@plt>
    req->iov[0].iov_len = READ_SZ;
    a343:	48 89 c7             	mov    %rax,%rdi
    a346:	e8 85 a3 ff ff       	call   46d0 <__asan_report_store8@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    a34b:	e8 80 a3 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->user_data = (unsigned long) data;
    a350:	e8 7b a3 ff ff       	call   46d0 <__asan_report_store8@plt>
    a355:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

000000000000a360 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    a360:	f3 0f 1e fa          	endbr64
    a364:	41 56                	push   %r14
    a366:	41 89 f6             	mov    %esi,%r14d
    a369:	41 55                	push   %r13
    a36b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    a36e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    a373:	41 54                	push   %r12
    a375:	55                   	push   %rbp
    a376:	53                   	push   %rbx
    a377:	48 89 d3             	mov    %rdx,%rbx
    void *buf = malloc(size);
    a37a:	e8 11 a2 ff ff       	call   4590 <malloc@plt>
    if (!buf) {
    a37f:	48 85 c0             	test   %rax,%rax
    a382:	0f 84 83 04 00 00    	je     a80b <_send_static_string_content+0x4ab>
    a388:	48 89 c5             	mov    %rax,%rbp
    unsigned long slen = strlen(str);
    a38b:	4c 89 ef             	mov    %r13,%rdi
    a38e:	e8 4d a2 ff ff       	call   45e0 <strlen@plt>
    req->iovec_count = 1;
    a393:	48 8d 7d 04          	lea    0x4(%rbp),%rdi
    unsigned long slen = strlen(str);
    a397:	49 89 c4             	mov    %rax,%r12
    req->iovec_count = 1;
    a39a:	48 89 f8             	mov    %rdi,%rax
    a39d:	48 c1 e8 03          	shr    $0x3,%rax
    a3a1:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    a3a8:	48 89 f8             	mov    %rdi,%rax
    a3ab:	83 e0 07             	and    $0x7,%eax
    a3ae:	83 c0 03             	add    $0x3,%eax
    a3b1:	38 d0                	cmp    %dl,%al
    a3b3:	7c 08                	jl     a3bd <_send_static_string_content+0x5d>
    a3b5:	84 d2                	test   %dl,%dl
    a3b7:	0f 85 20 04 00 00    	jne    a7dd <_send_static_string_content+0x47d>
    req->client_socket = client_socket;
    a3bd:	48 8d 7d 08          	lea    0x8(%rbp),%rdi
    req->iovec_count = 1;
    a3c1:	c7 45 04 01 00 00 00 	movl   $0x1,0x4(%rbp)
    req->client_socket = client_socket;
    a3c8:	48 89 f8             	mov    %rdi,%rax
    a3cb:	48 c1 e8 03          	shr    $0x3,%rax
    a3cf:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    a3d6:	84 c0                	test   %al,%al
    a3d8:	74 08                	je     a3e2 <_send_static_string_content+0x82>
    a3da:	3c 03                	cmp    $0x3,%al
    a3dc:	0f 8e 00 04 00 00    	jle    a7e2 <_send_static_string_content+0x482>
    a3e2:	44 89 75 08          	mov    %r14d,0x8(%rbp)
    void *buf = malloc(size);
    a3e6:	4c 89 e7             	mov    %r12,%rdi
    a3e9:	e8 a2 a1 ff ff       	call   4590 <malloc@plt>
    a3ee:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    a3f1:	48 85 c0             	test   %rax,%rax
    a3f4:	0f 84 58 04 00 00    	je     a852 <_send_static_string_content+0x4f2>
    req->iov[0].iov_base = zh_malloc(slen);
    a3fa:	4c 8d 75 10          	lea    0x10(%rbp),%r14
    a3fe:	4c 89 f0             	mov    %r14,%rax
    a401:	48 c1 e8 03          	shr    $0x3,%rax
    a405:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    a40c:	0f 85 f1 03 00 00    	jne    a803 <_send_static_string_content+0x4a3>
    req->iov[0].iov_len = slen;
    a412:	48 8d 45 18          	lea    0x18(%rbp),%rax
    req->iov[0].iov_base = zh_malloc(slen);
    a416:	48 89 7d 10          	mov    %rdi,0x10(%rbp)
    req->iov[0].iov_len = slen;
    a41a:	48 89 c2             	mov    %rax,%rdx
    a41d:	48 c1 ea 03          	shr    $0x3,%rdx
    a421:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    a428:	0f 85 c8 03 00 00    	jne    a7f6 <_send_static_string_content+0x496>
    a42e:	4c 89 65 18          	mov    %r12,0x18(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    a432:	4c 89 e2             	mov    %r12,%rdx
    a435:	4c 89 ee             	mov    %r13,%rsi
    a438:	e8 83 a0 ff ff       	call   44c0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    a43d:	48 8d 7b 44          	lea    0x44(%rbx),%rdi
    a441:	48 89 f8             	mov    %rdi,%rax
    a444:	48 c1 e8 03          	shr    $0x3,%rax
    a448:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    a44f:	48 89 f8             	mov    %rdi,%rax
    a452:	83 e0 07             	and    $0x7,%eax
    a455:	83 c0 03             	add    $0x3,%eax
    a458:	38 d0                	cmp    %dl,%al
    a45a:	7c 08                	jl     a464 <_send_static_string_content+0x104>
    a45c:	84 d2                	test   %dl,%dl
    a45e:	0f 85 74 03 00 00    	jne    a7d8 <_send_static_string_content+0x478>
	if (ring->flags & IORING_SETUP_SQE128)
    a464:	48 8d bb c0 00 00 00 	lea    0xc0(%rbx),%rdi
	unsigned int head, next = sq->sqe_tail + 1;
    a46b:	8b 43 44             	mov    0x44(%rbx),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    a46e:	48 89 fa             	mov    %rdi,%rdx
    a471:	48 c1 ea 03          	shr    $0x3,%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    a475:	83 c0 01             	add    $0x1,%eax
	if (ring->flags & IORING_SETUP_SQE128)
    a478:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    a47f:	84 d2                	test   %dl,%dl
    a481:	74 09                	je     a48c <_send_static_string_content+0x12c>
    a483:	80 fa 03             	cmp    $0x3,%dl
    a486:	0f 8e 5b 03 00 00    	jle    a7e7 <_send_static_string_content+0x487>
    a48c:	8b 8b c0 00 00 00    	mov    0xc0(%rbx),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    a492:	48 89 da             	mov    %rbx,%rdx
    a495:	48 c1 ea 03          	shr    $0x3,%rdx
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    a499:	f6 c1 02             	test   $0x2,%cl
    a49c:	0f 85 fe 02 00 00    	jne    a7a0 <_send_static_string_content+0x440>
		head = IO_URING_READ_ONCE(*sq->khead);
    a4a2:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    a4a9:	0f 85 41 04 00 00    	jne    a8f0 <_send_static_string_content+0x590>
    a4af:	48 8b 3b             	mov    (%rbx),%rdi
    a4b2:	48 89 fa             	mov    %rdi,%rdx
    a4b5:	48 c1 ea 03          	shr    $0x3,%rdx
    a4b9:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    a4c0:	48 89 fa             	mov    %rdi,%rdx
    a4c3:	83 e2 07             	and    $0x7,%edx
    a4c6:	83 c2 03             	add    $0x3,%edx
    a4c9:	40 38 f2             	cmp    %sil,%dl
    a4cc:	7c 09                	jl     a4d7 <_send_static_string_content+0x177>
    a4ce:	40 84 f6             	test   %sil,%sil
    a4d1:	0f 85 15 03 00 00    	jne    a7ec <_send_static_string_content+0x48c>
    a4d7:	8b 17                	mov    (%rdi),%edx
	if (next - head <= sq->ring_entries) {
    a4d9:	48 8d 7b 5c          	lea    0x5c(%rbx),%rdi
    a4dd:	41 89 c0             	mov    %eax,%r8d
    a4e0:	41 29 d0             	sub    %edx,%r8d
    a4e3:	48 89 fa             	mov    %rdi,%rdx
    a4e6:	48 c1 ea 03          	shr    $0x3,%rdx
    a4ea:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    a4f1:	48 89 fa             	mov    %rdi,%rdx
    a4f4:	83 e2 07             	and    $0x7,%edx
    a4f7:	83 c2 03             	add    $0x3,%edx
    a4fa:	40 38 f2             	cmp    %sil,%dl
    a4fd:	7c 09                	jl     a508 <_send_static_string_content+0x1a8>
    a4ff:	40 84 f6             	test   %sil,%sil
    a502:	0f 85 f6 02 00 00    	jne    a7fe <_send_static_string_content+0x49e>
    a508:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    a50c:	0f 82 5d a4 ff ff    	jb     496f <_send_static_string_content.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    a512:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    a516:	48 89 fa             	mov    %rdi,%rdx
    a519:	48 c1 ea 03          	shr    $0x3,%rdx
    a51d:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    a524:	0f 85 69 03 00 00    	jne    a893 <_send_static_string_content+0x533>
    a52a:	4c 8d 43 58          	lea    0x58(%rbx),%r8
    a52e:	48 8b 7b 38          	mov    0x38(%rbx),%rdi
    a532:	8b 53 44             	mov    0x44(%rbx),%edx
    a535:	4c 89 c6             	mov    %r8,%rsi
    a538:	48 c1 ee 03          	shr    $0x3,%rsi
    a53c:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    a543:	40 84 f6             	test   %sil,%sil
    a546:	74 0a                	je     a552 <_send_static_string_content+0x1f2>
    a548:	40 80 fe 03          	cmp    $0x3,%sil
    a54c:	0f 8e 46 03 00 00    	jle    a898 <_send_static_string_content+0x538>
		sq->sqe_tail = next;
    a552:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    a555:	c1 e9 0a             	shr    $0xa,%ecx
    req->event_type = EVENT_TYPE_WRITE;
    a558:	48 89 e8             	mov    %rbp,%rax
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    a55b:	23 53 58             	and    0x58(%rbx),%edx
	if (ring->flags & IORING_SETUP_SQE128)
    a55e:	83 e1 01             	and    $0x1,%ecx
    a561:	48 c1 e8 03          	shr    $0x3,%rax
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    a565:	d3 e2                	shl    %cl,%edx
    a567:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    a56e:	48 c1 e2 06          	shl    $0x6,%rdx
    a572:	48 01 d7             	add    %rdx,%rdi
    a575:	84 c0                	test   %al,%al
    a577:	74 08                	je     a581 <_send_static_string_content+0x221>
    a579:	3c 03                	cmp    $0x3,%al
    a57b:	0f 8e ed 02 00 00    	jle    a86e <_send_static_string_content+0x50e>
	sqe->opcode = (__u8) op;
    a581:	48 89 f8             	mov    %rdi,%rax
    a584:	c7 45 00 02 00 00 00 	movl   $0x2,0x0(%rbp)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    a58b:	8b 75 04             	mov    0x4(%rbp),%esi
    a58e:	48 c1 e8 03          	shr    $0x3,%rax
    a592:	44 8b 45 08          	mov    0x8(%rbp),%r8d
    a596:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    a59d:	84 c0                	test   %al,%al
    a59f:	74 06                	je     a5a7 <_send_static_string_content+0x247>
    a5a1:	0f 8e cf 02 00 00    	jle    a876 <_send_static_string_content+0x516>
	sqe->flags = 0;
    a5a7:	48 8d 47 01          	lea    0x1(%rdi),%rax
	sqe->opcode = (__u8) op;
    a5ab:	c6 07 02             	movb   $0x2,(%rdi)
	sqe->flags = 0;
    a5ae:	48 89 c2             	mov    %rax,%rdx
    a5b1:	48 89 c1             	mov    %rax,%rcx
    a5b4:	48 c1 ea 03          	shr    $0x3,%rdx
    a5b8:	83 e1 07             	and    $0x7,%ecx
    a5bb:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    a5c2:	38 ca                	cmp    %cl,%dl
    a5c4:	7f 08                	jg     a5ce <_send_static_string_content+0x26e>
    a5c6:	84 d2                	test   %dl,%dl
    a5c8:	0f 85 ad 02 00 00    	jne    a87b <_send_static_string_content+0x51b>
	sqe->ioprio = 0;
    a5ce:	48 8d 57 02          	lea    0x2(%rdi),%rdx
	sqe->flags = 0;
    a5d2:	c6 47 01 00          	movb   $0x0,0x1(%rdi)
	sqe->ioprio = 0;
    a5d6:	48 89 d0             	mov    %rdx,%rax
    a5d9:	48 c1 e8 03          	shr    $0x3,%rax
    a5dd:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    a5e4:	48 89 d0             	mov    %rdx,%rax
    a5e7:	83 e0 07             	and    $0x7,%eax
    a5ea:	83 c0 01             	add    $0x1,%eax
    a5ed:	38 c8                	cmp    %cl,%al
    a5ef:	7c 08                	jl     a5f9 <_send_static_string_content+0x299>
    a5f1:	84 c9                	test   %cl,%cl
    a5f3:	0f 85 b7 02 00 00    	jne    a8b0 <_send_static_string_content+0x550>
	sqe->fd = fd;
    a5f9:	48 8d 57 04          	lea    0x4(%rdi),%rdx
	sqe->ioprio = 0;
    a5fd:	31 c9                	xor    %ecx,%ecx
	sqe->fd = fd;
    a5ff:	48 89 d0             	mov    %rdx,%rax
	sqe->ioprio = 0;
    a602:	66 89 4f 02          	mov    %cx,0x2(%rdi)
	sqe->fd = fd;
    a606:	48 c1 e8 03          	shr    $0x3,%rax
    a60a:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    a611:	48 89 d0             	mov    %rdx,%rax
    a614:	83 e0 07             	and    $0x7,%eax
    a617:	83 c0 03             	add    $0x3,%eax
    a61a:	38 c8                	cmp    %cl,%al
    a61c:	7c 08                	jl     a626 <_send_static_string_content+0x2c6>
    a61e:	84 c9                	test   %cl,%cl
    a620:	0f 85 92 02 00 00    	jne    a8b8 <_send_static_string_content+0x558>
	sqe->off = offset;
    a626:	48 8d 47 08          	lea    0x8(%rdi),%rax
	sqe->fd = fd;
    a62a:	44 89 47 04          	mov    %r8d,0x4(%rdi)
	sqe->off = offset;
    a62e:	48 89 c2             	mov    %rax,%rdx
    a631:	48 c1 ea 03          	shr    $0x3,%rdx
    a635:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    a63c:	0f 85 7e 02 00 00    	jne    a8c0 <_send_static_string_content+0x560>
	sqe->addr = (unsigned long) addr;
    a642:	48 8d 47 10          	lea    0x10(%rdi),%rax
	sqe->off = offset;
    a646:	48 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%rdi)
	sqe->addr = (unsigned long) addr;
    a64e:	48 89 c2             	mov    %rax,%rdx
    a651:	48 c1 ea 03          	shr    $0x3,%rdx
    a655:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    a65c:	0f 85 66 02 00 00    	jne    a8c8 <_send_static_string_content+0x568>
	sqe->len = len;
    a662:	48 8d 57 18          	lea    0x18(%rdi),%rdx
	sqe->addr = (unsigned long) addr;
    a666:	4c 89 77 10          	mov    %r14,0x10(%rdi)
	sqe->len = len;
    a66a:	48 89 d0             	mov    %rdx,%rax
    a66d:	48 c1 e8 03          	shr    $0x3,%rax
    a671:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    a678:	84 c0                	test   %al,%al
    a67a:	74 08                	je     a684 <_send_static_string_content+0x324>
    a67c:	3c 03                	cmp    $0x3,%al
    a67e:	0f 8e 4c 02 00 00    	jle    a8d0 <_send_static_string_content+0x570>
	sqe->rw_flags = 0;
    a684:	48 8d 57 1c          	lea    0x1c(%rdi),%rdx
	sqe->len = len;
    a688:	89 77 18             	mov    %esi,0x18(%rdi)
	sqe->rw_flags = 0;
    a68b:	48 89 d0             	mov    %rdx,%rax
    a68e:	48 c1 e8 03          	shr    $0x3,%rax
    a692:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    a699:	48 89 d0             	mov    %rdx,%rax
    a69c:	83 e0 07             	and    $0x7,%eax
    a69f:	83 c0 03             	add    $0x3,%eax
    a6a2:	38 c8                	cmp    %cl,%al
    a6a4:	7c 08                	jl     a6ae <_send_static_string_content+0x34e>
    a6a6:	84 c9                	test   %cl,%cl
    a6a8:	0f 85 f2 01 00 00    	jne    a8a0 <_send_static_string_content+0x540>
	sqe->buf_index = 0;
    a6ae:	48 8d 57 28          	lea    0x28(%rdi),%rdx
	sqe->rw_flags = 0;
    a6b2:	c7 47 1c 00 00 00 00 	movl   $0x0,0x1c(%rdi)
	sqe->buf_index = 0;
    a6b9:	48 89 d0             	mov    %rdx,%rax
    a6bc:	48 c1 e8 03          	shr    $0x3,%rax
    a6c0:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    a6c7:	84 c0                	test   %al,%al
    a6c9:	74 08                	je     a6d3 <_send_static_string_content+0x373>
    a6cb:	3c 01                	cmp    $0x1,%al
    a6cd:	0f 8e d5 01 00 00    	jle    a8a8 <_send_static_string_content+0x548>
    a6d3:	31 d2                	xor    %edx,%edx
    a6d5:	66 89 57 28          	mov    %dx,0x28(%rdi)
	sqe->personality = 0;
    a6d9:	48 8d 57 2a          	lea    0x2a(%rdi),%rdx
    a6dd:	48 89 d0             	mov    %rdx,%rax
    a6e0:	48 c1 e8 03          	shr    $0x3,%rax
    a6e4:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    a6eb:	48 89 d0             	mov    %rdx,%rax
    a6ee:	83 e0 07             	and    $0x7,%eax
    a6f1:	83 c0 01             	add    $0x1,%eax
    a6f4:	38 c8                	cmp    %cl,%al
    a6f6:	7c 08                	jl     a700 <_send_static_string_content+0x3a0>
    a6f8:	84 c9                	test   %cl,%cl
    a6fa:	0f 85 83 01 00 00    	jne    a883 <_send_static_string_content+0x523>
    a700:	31 c0                	xor    %eax,%eax
	sqe->file_index = 0;
    a702:	48 8d 57 2c          	lea    0x2c(%rdi),%rdx
	sqe->personality = 0;
    a706:	66 89 47 2a          	mov    %ax,0x2a(%rdi)
	sqe->file_index = 0;
    a70a:	48 89 d0             	mov    %rdx,%rax
    a70d:	48 c1 e8 03          	shr    $0x3,%rax
    a711:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    a718:	48 89 d0             	mov    %rdx,%rax
    a71b:	83 e0 07             	and    $0x7,%eax
    a71e:	83 c0 03             	add    $0x3,%eax
    a721:	38 c8                	cmp    %cl,%al
    a723:	7c 08                	jl     a72d <_send_static_string_content+0x3cd>
    a725:	84 c9                	test   %cl,%cl
    a727:	0f 85 5e 01 00 00    	jne    a88b <_send_static_string_content+0x52b>
	sqe->addr3 = 0;
    a72d:	48 8d 47 30          	lea    0x30(%rdi),%rax
	sqe->file_index = 0;
    a731:	c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%rdi)
	sqe->addr3 = 0;
    a738:	48 89 c2             	mov    %rax,%rdx
    a73b:	48 c1 ea 03          	shr    $0x3,%rdx
    a73f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    a746:	0f 85 94 01 00 00    	jne    a8e0 <_send_static_string_content+0x580>
	sqe->__pad2[0] = 0;
    a74c:	48 8d 47 38          	lea    0x38(%rdi),%rax
	sqe->addr3 = 0;
    a750:	48 c7 47 30 00 00 00 00 	movq   $0x0,0x30(%rdi)
	sqe->__pad2[0] = 0;
    a758:	48 89 c2             	mov    %rax,%rdx
    a75b:	48 c1 ea 03          	shr    $0x3,%rdx
    a75f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    a766:	0f 85 7c 01 00 00    	jne    a8e8 <_send_static_string_content+0x588>
	sqe->user_data = (unsigned long) data;
    a76c:	48 8d 47 20          	lea    0x20(%rdi),%rax
	sqe->__pad2[0] = 0;
    a770:	48 c7 47 38 00 00 00 00 	movq   $0x0,0x38(%rdi)
	sqe->user_data = (unsigned long) data;
    a778:	48 89 c2             	mov    %rax,%rdx
    a77b:	48 c1 ea 03          	shr    $0x3,%rdx
    a77f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    a786:	0f 85 4c 01 00 00    	jne    a8d8 <_send_static_string_content+0x578>
    a78c:	48 89 6f 20          	mov    %rbp,0x20(%rdi)
    io_uring_submit(ring);
    a790:	48 89 df             	mov    %rbx,%rdi
}
    a793:	5b                   	pop    %rbx
    a794:	5d                   	pop    %rbp
    a795:	41 5c                	pop    %r12
    a797:	41 5d                	pop    %r13
    a799:	41 5e                	pop    %r14
    io_uring_submit(ring);
    a79b:	e9 c0 9e ff ff       	jmp    4660 <io_uring_submit@plt>
		head = io_uring_smp_load_acquire(sq->khead);
    a7a0:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    a7a7:	0f 85 4b 01 00 00    	jne    a8f8 <_send_static_string_content+0x598>
    a7ad:	48 8b 3b             	mov    (%rbx),%rdi
    a7b0:	48 89 fa             	mov    %rdi,%rdx
    a7b3:	48 c1 ea 03          	shr    $0x3,%rdx
    a7b7:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    a7be:	48 89 fa             	mov    %rdi,%rdx
    a7c1:	83 e2 07             	and    $0x7,%edx
    a7c4:	83 c2 03             	add    $0x3,%edx
    a7c7:	40 38 f2             	cmp    %sil,%dl
    a7ca:	7c 05                	jl     a7d1 <_send_static_string_content+0x471>
    a7cc:	40 84 f6             	test   %sil,%sil
    a7cf:	75 20                	jne    a7f1 <_send_static_string_content+0x491>
    a7d1:	8b 17                	mov    (%rdi),%edx
    a7d3:	e9 01 fd ff ff       	jmp    a4d9 <_send_static_string_content+0x179>
	unsigned int head, next = sq->sqe_tail + 1;
    a7d8:	e8 73 9d ff ff       	call   4550 <__asan_report_load4@plt>
    req->iovec_count = 1;
    a7dd:	e8 de 9e ff ff       	call   46c0 <__asan_report_store4@plt>
    req->client_socket = client_socket;
    a7e2:	e8 d9 9e ff ff       	call   46c0 <__asan_report_store4@plt>
	if (ring->flags & IORING_SETUP_SQE128)
    a7e7:	e8 64 9d ff ff       	call   4550 <__asan_report_load4@plt>
		head = IO_URING_READ_ONCE(*sq->khead);
    a7ec:	e8 5f 9d ff ff       	call   4550 <__asan_report_load4@plt>
		head = io_uring_smp_load_acquire(sq->khead);
    a7f1:	e8 5a 9d ff ff       	call   4550 <__asan_report_load4@plt>
    req->iov[0].iov_len = slen;
    a7f6:	48 89 c7             	mov    %rax,%rdi
    a7f9:	e8 d2 9e ff ff       	call   46d0 <__asan_report_store8@plt>
	if (next - head <= sq->ring_entries) {
    a7fe:	e8 4d 9d ff ff       	call   4550 <__asan_report_load4@plt>
    req->iov[0].iov_base = zh_malloc(slen);
    a803:	4c 89 f7             	mov    %r14,%rdi
    a806:	e8 c5 9e ff ff       	call   46d0 <__asan_report_store8@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    a80b:	48 8d 3d 8e b3 00 00 	lea    0xb38e(%rip),%rdi        # 15ba0 <stderr@GLIBC_2.2.5>
    a812:	48 89 f8             	mov    %rdi,%rax
    a815:	48 c1 e8 03          	shr    $0x3,%rax
    a819:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    a820:	0f 85 da 00 00 00    	jne    a900 <_send_static_string_content+0x5a0>
    a826:	48 8b 0d 73 b3 00 00 	mov    0xb373(%rip),%rcx        # 15ba0 <stderr@GLIBC_2.2.5>
    a82d:	ba 28 00 00 00       	mov    $0x28,%edx
    a832:	be 01 00 00 00       	mov    $0x1,%esi
    a837:	48 8d 3d 22 5a 00 00 	lea    0x5a22(%rip),%rdi        # 10260 <_IO_stdin_used+0x260>
    a83e:	e8 5d 9c ff ff       	call   44a0 <fwrite@plt>
        exit(1);
    a843:	e8 c8 9d ff ff       	call   4610 <__asan_handle_no_return@plt>
    a848:	bf 01 00 00 00       	mov    $0x1,%edi
    a84d:	e8 be 9c ff ff       	call   4510 <exit@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    a852:	48 8d 3d 47 b3 00 00 	lea    0xb347(%rip),%rdi        # 15ba0 <stderr@GLIBC_2.2.5>
    a859:	48 89 f8             	mov    %rdi,%rax
    a85c:	48 c1 e8 03          	shr    $0x3,%rax
    a860:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    a867:	74 bd                	je     a826 <_send_static_string_content+0x4c6>
    a869:	e8 72 9c ff ff       	call   44e0 <__asan_report_load8@plt>
    req->event_type = EVENT_TYPE_WRITE;
    a86e:	48 89 ef             	mov    %rbp,%rdi
    a871:	e8 4a 9e ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->opcode = (__u8) op;
    a876:	e8 55 9f ff ff       	call   47d0 <__asan_report_store1@plt>
	sqe->flags = 0;
    a87b:	48 89 c7             	mov    %rax,%rdi
    a87e:	e8 4d 9f ff ff       	call   47d0 <__asan_report_store1@plt>
	sqe->personality = 0;
    a883:	48 89 d7             	mov    %rdx,%rdi
    a886:	e8 75 9c ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->file_index = 0;
    a88b:	48 89 d7             	mov    %rdx,%rdi
    a88e:	e8 2d 9e ff ff       	call   46c0 <__asan_report_store4@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    a893:	e8 48 9c ff ff       	call   44e0 <__asan_report_load8@plt>
    a898:	4c 89 c7             	mov    %r8,%rdi
    a89b:	e8 b0 9c ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->rw_flags = 0;
    a8a0:	48 89 d7             	mov    %rdx,%rdi
    a8a3:	e8 18 9e ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->buf_index = 0;
    a8a8:	48 89 d7             	mov    %rdx,%rdi
    a8ab:	e8 50 9c ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->ioprio = 0;
    a8b0:	48 89 d7             	mov    %rdx,%rdi
    a8b3:	e8 48 9c ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->fd = fd;
    a8b8:	48 89 d7             	mov    %rdx,%rdi
    a8bb:	e8 00 9e ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->off = offset;
    a8c0:	48 89 c7             	mov    %rax,%rdi
    a8c3:	e8 08 9e ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->addr = (unsigned long) addr;
    a8c8:	48 89 c7             	mov    %rax,%rdi
    a8cb:	e8 00 9e ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->len = len;
    a8d0:	48 89 d7             	mov    %rdx,%rdi
    a8d3:	e8 e8 9d ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->user_data = (unsigned long) data;
    a8d8:	48 89 c7             	mov    %rax,%rdi
    a8db:	e8 f0 9d ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->addr3 = 0;
    a8e0:	48 89 c7             	mov    %rax,%rdi
    a8e3:	e8 e8 9d ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->__pad2[0] = 0;
    a8e8:	48 89 c7             	mov    %rax,%rdi
    a8eb:	e8 e0 9d ff ff       	call   46d0 <__asan_report_store8@plt>
		head = IO_URING_READ_ONCE(*sq->khead);
    a8f0:	48 89 df             	mov    %rbx,%rdi
    a8f3:	e8 e8 9b ff ff       	call   44e0 <__asan_report_load8@plt>
		head = io_uring_smp_load_acquire(sq->khead);
    a8f8:	48 89 df             	mov    %rbx,%rdi
    a8fb:	e8 e0 9b ff ff       	call   44e0 <__asan_report_load8@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    a900:	e8 db 9b ff ff       	call   44e0 <__asan_report_load8@plt>
    a905:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

000000000000a910 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    a910:	f3 0f 1e fa          	endbr64
    a914:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    a917:	89 fe                	mov    %edi,%esi
    a919:	48 8b 3d 40 97 00 00 	mov    0x9740(%rip),%rdi        # 14060 <unimplemented_content>
    a920:	e9 3b fa ff ff       	jmp    a360 <_send_static_string_content>
    a925:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

000000000000a930 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    a930:	f3 0f 1e fa          	endbr64
    a934:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    a937:	89 fe                	mov    %edi,%esi
    a939:	48 8b 3d e0 96 00 00 	mov    0x96e0(%rip),%rdi        # 14020 <http_404_content>
    a940:	e9 1b fa ff ff       	jmp    a360 <_send_static_string_content>
    a945:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

000000000000a950 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    a950:	f3 0f 1e fa          	endbr64
    a954:	41 57                	push   %r15
    a956:	41 56                	push   %r14
    a958:	41 55                	push   %r13
    a95a:	41 54                	push   %r12
    a95c:	49 89 fc             	mov    %rdi,%r12
    a95f:	55                   	push   %rbp
    a960:	53                   	push   %rbx
    a961:	48 81 ec c8 05 00 00 	sub    $0x5c8,%rsp
    a968:	8b 05 12 b2 00 00    	mov    0xb212(%rip),%eax        # 15b80 <__asan_option_detect_stack_use_after_return@@Base>
    a96e:	48 8d 5c 24 20       	lea    0x20(%rsp),%rbx
    a973:	89 74 24 10          	mov    %esi,0x10(%rsp)
    a977:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    a97c:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    a981:	85 c0                	test   %eax,%eax
    a983:	0f 85 66 03 00 00    	jne    acef <handle_get_method+0x39f>
    a989:	48 8d 05 28 76 00 00 	lea    0x7628(%rip),%rax        # 11fb8 <_IO_stdin_used+0x1fb8>
    a990:	49 89 df             	mov    %rbx,%r15
    a993:	48 c7 03 b3 8a b5 41 	movq   $0x41b58ab3,(%rbx)
    if (path[strlen(path) - 1] == '/') {
    a99a:	4c 89 e7             	mov    %r12,%rdi
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    a99d:	48 89 43 08          	mov    %rax,0x8(%rbx)
    a9a1:	49 c1 ef 03          	shr    $0x3,%r15
    a9a5:	48 8d 05 a4 ff ff ff 	lea    -0x5c(%rip),%rax        # a950 <handle_get_method>
    a9ac:	48 8d ab a0 05 00 00 	lea    0x5a0(%rbx),%rbp
    a9b3:	48 89 43 10          	mov    %rax,0x10(%rbx)
    a9b7:	41 c7 87 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%r15)
    a9c2:	41 c7 87 04 80 ff 7f f1 f1 00 00 	movl   $0xf1f1,0x7fff8004(%r15)
    a9cd:	41 c7 87 18 80 ff 7f f2 f2 f2 f2 	movl   $0xf2f2f2f2,0x7fff8018(%r15)
    a9d8:	41 c7 87 1c 80 ff 7f f2 f2 f2 f2 	movl   $0xf2f2f2f2,0x7fff801c(%r15)
    a9e3:	41 c7 87 a0 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff80a0(%r15)
    a9ee:	41 c7 87 a4 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff80a4(%r15)
    a9f9:	41 c7 87 a8 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff80a8(%r15)
    aa04:	41 c7 87 ac 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff80ac(%r15)
    aa0f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    aa18:	48 89 84 24 b8 05 00 00 	mov    %rax,0x5b8(%rsp)
    aa20:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    aa22:	e8 b9 9b ff ff       	call   45e0 <strlen@plt>
    aa27:	49 8d 7c 04 ff       	lea    -0x1(%r12,%rax,1),%rdi
    aa2c:	49 89 c6             	mov    %rax,%r14
    aa2f:	48 89 f8             	mov    %rdi,%rax
    aa32:	48 89 fa             	mov    %rdi,%rdx
    aa35:	48 c1 e8 03          	shr    $0x3,%rax
    aa39:	83 e2 07             	and    $0x7,%edx
    aa3c:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    aa43:	38 d0                	cmp    %dl,%al
    aa45:	7f 08                	jg     aa4f <handle_get_method+0xff>
    aa47:	84 c0                	test   %al,%al
    aa49:	0f 85 8c 02 00 00    	jne    acdb <handle_get_method+0x38b>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    aa4f:	4c 8d ad 60 fb ff ff 	lea    -0x4a0(%rbp),%r13
    aa56:	80 3f 2f             	cmpb   $0x2f,(%rdi)
    aa59:	ba 06 00 00 00       	mov    $0x6,%edx
    aa5e:	48 8d 35 3b 5e 00 00 	lea    0x5e3b(%rip),%rsi        # 108a0 <_IO_stdin_used+0x8a0>
    aa65:	4c 89 ef             	mov    %r13,%rdi
    aa68:	0f 84 f2 00 00 00    	je     ab60 <handle_get_method+0x210>
    aa6e:	e8 4d 9a ff ff       	call   44c0 <memcpy@plt>


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    aa73:	49 8d 56 01          	lea    0x1(%r14),%rdx
    aa77:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    aa7c:	4c 89 e6             	mov    %r12,%rsi
    aa7f:	48 8d bd 66 fb ff ff 	lea    -0x49a(%rbp),%rdi
    aa86:	e8 25 9b ff ff       	call   45b0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    aa8b:	48 8d b5 90 fa ff ff 	lea    -0x570(%rbp),%rsi
    aa92:	4c 89 ef             	mov    %r13,%rdi
    aa95:	e8 56 9b ff ff       	call   45f0 <stat@plt>
    aa9a:	83 f8 ff             	cmp    $0xffffffff,%eax
    aa9d:	0f 84 05 02 00 00    	je     aca8 <handle_get_method+0x358>
        if (S_ISREG(path_stat.st_mode)) {
    aaa3:	48 8d bd a8 fa ff ff 	lea    -0x558(%rbp),%rdi
    aaaa:	48 89 f8             	mov    %rdi,%rax
    aaad:	48 c1 e8 03          	shr    $0x3,%rax
    aab1:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    aab8:	84 c0                	test   %al,%al
    aaba:	74 08                	je     aac4 <handle_get_method+0x174>
    aabc:	3c 03                	cmp    $0x3,%al
    aabe:	0f 8e 1c 02 00 00    	jle    ace0 <handle_get_method+0x390>
    aac4:	8b 85 a8 fa ff ff    	mov    -0x558(%rbp),%eax
    aaca:	25 00 f0 00 00       	and    $0xf000,%eax
    aacf:	3d 00 80 00 00       	cmp    $0x8000,%eax
    aad4:	0f 84 c6 00 00 00    	je     aba0 <handle_get_method+0x250>
    _send_static_string_content(http_404_content, client_socket, ring);
    aada:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    aadf:	8b 74 24 10          	mov    0x10(%rsp),%esi
    aae3:	48 8b 3d 36 95 00 00 	mov    0x9536(%rip),%rdi        # 14020 <http_404_content>
    aaea:	e8 71 f8 ff ff       	call   a360 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    aaef:	4c 89 ea             	mov    %r13,%rdx
    aaf2:	bf 01 00 00 00       	mov    $0x1,%edi
    aaf7:	31 c0                	xor    %eax,%eax
    aaf9:	48 8d 35 a0 5e 00 00 	lea    0x5ea0(%rip),%rsi        # 109a0 <_IO_stdin_used+0x9a0>
    ab00:	e8 1b 9a ff ff       	call   4520 <__printf_chk@plt>
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    ab05:	48 39 5c 24 08       	cmp    %rbx,0x8(%rsp)
    ab0a:	0f 85 f5 01 00 00    	jne    ad05 <handle_get_method+0x3b5>
    ab10:	49 c7 87 00 80 ff 7f 00 00 00 00 	movq   $0x0,0x7fff8000(%r15)
    ab1b:	66 0f ef c0          	pxor   %xmm0,%xmm0
    ab1f:	49 c7 87 18 80 ff 7f 00 00 00 00 	movq   $0x0,0x7fff8018(%r15)
    ab2a:	41 0f 11 87 a0 80 ff 7f 	movups %xmm0,0x7fff80a0(%r15)
}
    ab32:	48 8b 84 24 b8 05 00 00 	mov    0x5b8(%rsp),%rax
    ab3a:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    ab43:	0f 85 da 01 00 00    	jne    ad23 <handle_get_method+0x3d3>
    ab49:	48 81 c4 c8 05 00 00 	add    $0x5c8,%rsp
    ab50:	5b                   	pop    %rbx
    ab51:	5d                   	pop    %rbp
    ab52:	41 5c                	pop    %r12
    ab54:	41 5d                	pop    %r13
    ab56:	41 5e                	pop    %r14
    ab58:	41 5f                	pop    %r15
    ab5a:	c3                   	ret
    ab5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    ab60:	e8 5b 99 ff ff       	call   44c0 <memcpy@plt>
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    ab65:	4c 89 f2             	mov    %r14,%rdx
    ab68:	4c 89 e6             	mov    %r12,%rsi
    ab6b:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    ab70:	48 8d bd 66 fb ff ff 	lea    -0x49a(%rbp),%rdi
    ab77:	e8 34 9a ff ff       	call   45b0 <__memcpy_chk@plt>
    ab7c:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    ab81:	4b 8d 7c 2e 06       	lea    0x6(%r14,%r13,1),%rdi
    ab86:	ba 0b 00 00 00       	mov    $0xb,%edx
    ab8b:	4c 29 f1             	sub    %r14,%rcx
    ab8e:	48 8d 35 4b 5d 00 00 	lea    0x5d4b(%rip),%rsi        # 108e0 <_IO_stdin_used+0x8e0>
    ab95:	e8 16 9a ff ff       	call   45b0 <__memcpy_chk@plt>
    ab9a:	e9 ec fe ff ff       	jmp    aa8b <handle_get_method+0x13b>
    ab9f:	90                   	nop
    void *buf = malloc(size);
    aba0:	bf 70 00 00 00       	mov    $0x70,%edi
    aba5:	e8 e6 99 ff ff       	call   4590 <malloc@plt>
    abaa:	49 89 c4             	mov    %rax,%r12
    if (!buf) {
    abad:	48 85 c0             	test   %rax,%rax
    abb0:	0f 84 84 01 00 00    	je     ad3a <handle_get_method+0x3ea>
            req->iovec_count = 6;
    abb6:	48 8d 78 04          	lea    0x4(%rax),%rdi
    abba:	48 89 f8             	mov    %rdi,%rax
    abbd:	48 c1 e8 03          	shr    $0x3,%rax
    abc1:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    abc8:	48 89 f8             	mov    %rdi,%rax
    abcb:	83 e0 07             	and    $0x7,%eax
    abce:	83 c0 03             	add    $0x3,%eax
    abd1:	38 d0                	cmp    %dl,%al
    abd3:	7c 08                	jl     abdd <handle_get_method+0x28d>
    abd5:	84 d2                	test   %dl,%dl
    abd7:	0f 85 08 01 00 00    	jne    ace5 <handle_get_method+0x395>
    abdd:	41 c7 44 24 04 06 00 00 00 	movl   $0x6,0x4(%r12)
            req->client_socket = client_socket;
    abe6:	49 8d 7c 24 08       	lea    0x8(%r12),%rdi
    abeb:	48 89 f8             	mov    %rdi,%rax
    abee:	48 c1 e8 03          	shr    $0x3,%rax
    abf2:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    abf9:	84 c0                	test   %al,%al
    abfb:	74 08                	je     ac05 <handle_get_method+0x2b5>
    abfd:	3c 03                	cmp    $0x3,%al
    abff:	0f 8e e5 00 00 00    	jle    acea <handle_get_method+0x39a>
    ac05:	8b 44 24 10          	mov    0x10(%rsp),%eax
            send_headers(final_path, path_stat.st_size, req->iov);
    ac09:	49 8d 54 24 10       	lea    0x10(%r12),%rdx
            req->client_socket = client_socket;
    ac0e:	41 89 44 24 08       	mov    %eax,0x8(%r12)
            send_headers(final_path, path_stat.st_size, req->iov);
    ac13:	48 8d 85 c0 fa ff ff 	lea    -0x540(%rbp),%rax
    ac1a:	49 89 c6             	mov    %rax,%r14
    ac1d:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    ac22:	49 c1 ee 03          	shr    $0x3,%r14
    ac26:	41 80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r14)
    ac2e:	0f 85 f4 00 00 00    	jne    ad28 <handle_get_method+0x3d8>
    ac34:	48 8b b5 c0 fa ff ff 	mov    -0x540(%rbp),%rsi
    ac3b:	4c 89 ef             	mov    %r13,%rdi
    ac3e:	e8 8d e4 ff ff       	call   90d0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    ac43:	41 80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r14)
    ac4b:	49 8d 54 24 60       	lea    0x60(%r12),%rdx
    ac50:	0f 85 da 00 00 00    	jne    ad30 <handle_get_method+0x3e0>
    ac56:	48 8b b5 c0 fa ff ff 	mov    -0x540(%rbp),%rsi
    ac5d:	4c 89 ef             	mov    %r13,%rdi
    ac60:	e8 2b ec ff ff       	call   9890 <copy_file_contents>
            printf("200 %s %ld bytes\n", final_path, path_stat.st_size);
    ac65:	41 80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r14)
    ac6d:	0f 85 0a 01 00 00    	jne    ad7d <handle_get_method+0x42d>
    ac73:	48 8b 8d c0 fa ff ff 	mov    -0x540(%rbp),%rcx
    ac7a:	4c 89 ea             	mov    %r13,%rdx
    ac7d:	bf 01 00 00 00       	mov    $0x1,%edi
    ac82:	31 c0                	xor    %eax,%eax
    ac84:	48 8d 35 d5 5c 00 00 	lea    0x5cd5(%rip),%rsi        # 10960 <_IO_stdin_used+0x960>
    ac8b:	e8 90 98 ff ff       	call   4520 <__printf_chk@plt>
            add_write_request(req, ring);
    ac90:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    ac95:	4c 89 e7             	mov    %r12,%rdi
    ac98:	e8 23 ed ff ff       	call   99c0 <add_write_request>
    ac9d:	e9 63 fe ff ff       	jmp    ab05 <handle_get_method+0x1b5>
    aca2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    aca8:	4c 89 ea             	mov    %r13,%rdx
    acab:	4c 89 e1             	mov    %r12,%rcx
    acae:	48 8d 35 6b 5c 00 00 	lea    0x5c6b(%rip),%rsi        # 10920 <_IO_stdin_used+0x920>
    acb5:	31 c0                	xor    %eax,%eax
    acb7:	bf 01 00 00 00       	mov    $0x1,%edi
    acbc:	e8 5f 98 ff ff       	call   4520 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    acc1:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    acc6:	8b 74 24 10          	mov    0x10(%rsp),%esi
    acca:	48 8b 3d 4f 93 00 00 	mov    0x934f(%rip),%rdi        # 14020 <http_404_content>
    acd1:	e8 8a f6 ff ff       	call   a360 <_send_static_string_content>
}
    acd6:	e9 2a fe ff ff       	jmp    ab05 <handle_get_method+0x1b5>
    if (path[strlen(path) - 1] == '/') {
    acdb:	e8 b0 9a ff ff       	call   4790 <__asan_report_load1@plt>
        if (S_ISREG(path_stat.st_mode)) {
    ace0:	e8 6b 98 ff ff       	call   4550 <__asan_report_load4@plt>
            req->iovec_count = 6;
    ace5:	e8 d6 99 ff ff       	call   46c0 <__asan_report_store4@plt>
            req->client_socket = client_socket;
    acea:	e8 d1 99 ff ff       	call   46c0 <__asan_report_store4@plt>
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    acef:	bf 80 05 00 00       	mov    $0x580,%edi
    acf4:	e8 77 9a ff ff       	call   4770 <__asan_stack_malloc_5@plt>
    acf9:	48 85 c0             	test   %rax,%rax
    acfc:	48 0f 45 d8          	cmovne %rax,%rbx
    ad00:	e9 84 fc ff ff       	jmp    a989 <handle_get_method+0x39>
    ad05:	48 c7 03 0e 36 e0 45 	movq   $0x45e0360e,(%rbx)
    ad0c:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    ad11:	be 80 05 00 00       	mov    $0x580,%esi
    ad16:	48 89 df             	mov    %rbx,%rdi
    ad19:	e8 62 99 ff ff       	call   4680 <__asan_stack_free_5@plt>
    ad1e:	e9 0f fe ff ff       	jmp    ab32 <handle_get_method+0x1e2>
}
    ad23:	e8 88 99 ff ff       	call   46b0 <__stack_chk_fail@plt>
            send_headers(final_path, path_stat.st_size, req->iov);
    ad28:	48 89 c7             	mov    %rax,%rdi
    ad2b:	e8 b0 97 ff ff       	call   44e0 <__asan_report_load8@plt>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    ad30:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    ad35:	e8 a6 97 ff ff       	call   44e0 <__asan_report_load8@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    ad3a:	48 8d 3d 5f ae 00 00 	lea    0xae5f(%rip),%rdi        # 15ba0 <stderr@GLIBC_2.2.5>
    ad41:	48 89 f8             	mov    %rdi,%rax
    ad44:	48 c1 e8 03          	shr    $0x3,%rax
    ad48:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ad4f:	75 36                	jne    ad87 <handle_get_method+0x437>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    ad51:	48 8b 0d 48 ae 00 00 	mov    0xae48(%rip),%rcx        # 15ba0 <stderr@GLIBC_2.2.5>
    ad58:	ba 28 00 00 00       	mov    $0x28,%edx
    ad5d:	be 01 00 00 00       	mov    $0x1,%esi
    ad62:	48 8d 3d f7 54 00 00 	lea    0x54f7(%rip),%rdi        # 10260 <_IO_stdin_used+0x260>
    ad69:	e8 32 97 ff ff       	call   44a0 <fwrite@plt>
        exit(1);
    ad6e:	e8 9d 98 ff ff       	call   4610 <__asan_handle_no_return@plt>
    ad73:	bf 01 00 00 00       	mov    $0x1,%edi
    ad78:	e8 93 97 ff ff       	call   4510 <exit@plt>
            printf("200 %s %ld bytes\n", final_path, path_stat.st_size);
    ad7d:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    ad82:	e8 59 97 ff ff       	call   44e0 <__asan_report_load8@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    ad87:	e8 54 97 ff ff       	call   44e0 <__asan_report_load8@plt>
    ad8c:	0f 1f 40 00          	nopl   0x0(%rax)

000000000000ad90 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    ad90:	f3 0f 1e fa          	endbr64
    ad94:	41 57                	push   %r15
    ad96:	41 56                	push   %r14
    ad98:	41 55                	push   %r13
    ad9a:	41 54                	push   %r12
    ad9c:	49 89 fc             	mov    %rdi,%r12
    ad9f:	55                   	push   %rbp
    ada0:	53                   	push   %rbx
    ada1:	48 83 ec 78          	sub    $0x78,%rsp
    ada5:	8b 05 d5 ad 00 00    	mov    0xadd5(%rip),%eax        # 15b80 <__asan_option_detect_stack_use_after_return@@Base>
    adab:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    adb0:	89 74 24 08          	mov    %esi,0x8(%rsp)
    adb4:	48 89 14 24          	mov    %rdx,(%rsp)
    adb8:	49 89 ef             	mov    %rbp,%r15
    adbb:	85 c0                	test   %eax,%eax
    adbd:	0f 85 d5 01 00 00    	jne    af98 <handle_http_method+0x208>
    adc3:	48 8d 05 56 73 00 00 	lea    0x7356(%rip),%rax        # 12120 <_IO_stdin_used+0x2120>
    adca:	48 89 eb             	mov    %rbp,%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    adcd:	48 8d 55 20          	lea    0x20(%rbp),%rdx
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    add1:	48 c7 45 00 b3 8a b5 41 	movq   $0x41b58ab3,0x0(%rbp)
    add9:	48 89 45 08          	mov    %rax,0x8(%rbp)
    addd:	48 c1 eb 03          	shr    $0x3,%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    ade1:	4c 89 e7             	mov    %r12,%rdi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    ade4:	4c 8d 6d 60          	lea    0x60(%rbp),%r13
    ade8:	48 8d 05 a1 ff ff ff 	lea    -0x5f(%rip),%rax        # ad90 <handle_http_method>
    method = strtok_r(method_buffer, " ", &saveptr);
    adef:	4c 8d 35 ea 5b 00 00 	lea    0x5bea(%rip),%r14        # 109e0 <_IO_stdin_used+0x9e0>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    adf6:	48 89 45 10          	mov    %rax,0x10(%rbp)
    method = strtok_r(method_buffer, " ", &saveptr);
    adfa:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    adfd:	c7 83 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%rbx)
    ae07:	c7 83 04 80 ff 7f 00 f3 f3 f3 	movl   $0xf3f3f300,0x7fff8004(%rbx)
    ae11:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    ae1a:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    ae1f:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    ae21:	e8 1a 98 ff ff       	call   4640 <strtok_r@plt>
    ae26:	49 89 c4             	mov    %rax,%r12
    for (; *str; ++str)
    ae29:	48 c1 e8 03          	shr    $0x3,%rax
    ae2d:	4c 89 e2             	mov    %r12,%rdx
    ae30:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    ae37:	83 e2 07             	and    $0x7,%edx
    ae3a:	38 d0                	cmp    %dl,%al
    ae3c:	7f 08                	jg     ae46 <handle_http_method+0xb6>
    ae3e:	84 c0                	test   %al,%al
    ae40:	0f 85 30 01 00 00    	jne    af76 <handle_http_method+0x1e6>
    ae46:	41 0f b6 14 24       	movzbl (%r12),%edx
    ae4b:	84 d2                	test   %dl,%dl
    ae4d:	88 54 24 0f          	mov    %dl,0xf(%rsp)
    ae51:	0f 84 aa 00 00 00    	je     af01 <handle_http_method+0x171>
        *str = (char)tolower(*str);
    ae57:	e8 94 98 ff ff       	call   46f0 <__ctype_tolower_loc@plt>
    ae5c:	48 0f be 54 24 0f    	movsbq 0xf(%rsp),%rdx
    ae62:	4c 89 e7             	mov    %r12,%rdi
    ae65:	49 89 c1             	mov    %rax,%r9
    ae68:	48 89 c6             	mov    %rax,%rsi
    ae6b:	49 c1 e9 03          	shr    $0x3,%r9
    ae6f:	90                   	nop
    ae70:	41 80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r9)
    ae78:	0f 85 12 01 00 00    	jne    af90 <handle_http_method+0x200>
    ae7e:	48 8b 06             	mov    (%rsi),%rax
    ae81:	48 8d 04 90          	lea    (%rax,%rdx,4),%rax
    ae85:	48 89 c2             	mov    %rax,%rdx
    ae88:	48 c1 ea 03          	shr    $0x3,%rdx
    ae8c:	44 0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%r10d
    ae94:	48 89 c2             	mov    %rax,%rdx
    ae97:	83 e2 07             	and    $0x7,%edx
    ae9a:	83 c2 03             	add    $0x3,%edx
    ae9d:	44 38 d2             	cmp    %r10b,%dl
    aea0:	7c 09                	jl     aeab <handle_http_method+0x11b>
    aea2:	45 84 d2             	test   %r10b,%r10b
    aea5:	0f 85 dd 00 00 00    	jne    af88 <handle_http_method+0x1f8>
    aeab:	8b 10                	mov    (%rax),%edx
    aead:	48 89 f8             	mov    %rdi,%rax
    aeb0:	49 89 fa             	mov    %rdi,%r10
    aeb3:	48 c1 e8 03          	shr    $0x3,%rax
    aeb7:	41 83 e2 07          	and    $0x7,%r10d
    aebb:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    aec2:	44 38 d0             	cmp    %r10b,%al
    aec5:	7f 08                	jg     aecf <handle_http_method+0x13f>
    aec7:	84 c0                	test   %al,%al
    aec9:	0f 85 b4 00 00 00    	jne    af83 <handle_http_method+0x1f3>
    aecf:	88 17                	mov    %dl,(%rdi)
    for (; *str; ++str)
    aed1:	48 83 c7 01          	add    $0x1,%rdi
    aed5:	48 89 f8             	mov    %rdi,%rax
    aed8:	48 89 fa             	mov    %rdi,%rdx
    aedb:	48 c1 e8 03          	shr    $0x3,%rax
    aedf:	83 e2 07             	and    $0x7,%edx
    aee2:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    aee9:	38 d0                	cmp    %dl,%al
    aeeb:	7f 08                	jg     aef5 <handle_http_method+0x165>
    aeed:	84 c0                	test   %al,%al
    aeef:	0f 85 89 00 00 00    	jne    af7e <handle_http_method+0x1ee>
    aef5:	48 0f be 17          	movsbq (%rdi),%rdx
    aef9:	84 d2                	test   %dl,%dl
    aefb:	0f 85 6f ff ff ff    	jne    ae70 <handle_http_method+0xe0>
    path = strtok_r(NULL, " ", &saveptr);
    af01:	49 8d 55 c0          	lea    -0x40(%r13),%rdx
    af05:	4c 89 f6             	mov    %r14,%rsi
    af08:	31 ff                	xor    %edi,%edi
    af0a:	e8 31 97 ff ff       	call   4640 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    af0f:	48 8d 35 0a 5b 00 00 	lea    0x5b0a(%rip),%rsi        # 10a20 <_IO_stdin_used+0xa20>
    af16:	4c 89 e7             	mov    %r12,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    af19:	49 89 c5             	mov    %rax,%r13
    if (strcmp(method, "get") == 0) {
    af1c:	e8 0f 98 ff ff       	call   4730 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    af21:	48 8b 14 24          	mov    (%rsp),%rdx
    af25:	8b 74 24 08          	mov    0x8(%rsp),%esi
    if (strcmp(method, "get") == 0) {
    af29:	85 c0                	test   %eax,%eax
    af2b:	75 3b                	jne    af68 <handle_http_method+0x1d8>
        handle_get_method(path, client_socket, ring);
    af2d:	4c 89 ef             	mov    %r13,%rdi
    af30:	e8 1b fa ff ff       	call   a950 <handle_get_method>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    af35:	49 39 ef             	cmp    %rbp,%r15
    af38:	75 74                	jne    afae <handle_http_method+0x21e>
    af3a:	48 c7 83 00 80 ff 7f 00 00 00 00 	movq   $0x0,0x7fff8000(%rbx)
}
    af45:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    af4a:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    af53:	75 7e                	jne    afd3 <handle_http_method+0x243>
    af55:	48 83 c4 78          	add    $0x78,%rsp
    af59:	5b                   	pop    %rbx
    af5a:	5d                   	pop    %rbp
    af5b:	41 5c                	pop    %r12
    af5d:	41 5d                	pop    %r13
    af5f:	41 5e                	pop    %r14
    af61:	41 5f                	pop    %r15
    af63:	c3                   	ret
    af64:	0f 1f 40 00          	nopl   0x0(%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    af68:	48 8b 3d f1 90 00 00 	mov    0x90f1(%rip),%rdi        # 14060 <unimplemented_content>
    af6f:	e8 ec f3 ff ff       	call   a360 <_send_static_string_content>
}
    af74:	eb bf                	jmp    af35 <handle_http_method+0x1a5>
    for (; *str; ++str)
    af76:	4c 89 e7             	mov    %r12,%rdi
    af79:	e8 12 98 ff ff       	call   4790 <__asan_report_load1@plt>
    af7e:	e8 0d 98 ff ff       	call   4790 <__asan_report_load1@plt>
        *str = (char)tolower(*str);
    af83:	e8 48 98 ff ff       	call   47d0 <__asan_report_store1@plt>
    af88:	48 89 c7             	mov    %rax,%rdi
    af8b:	e8 c0 95 ff ff       	call   4550 <__asan_report_load4@plt>
    af90:	48 89 f7             	mov    %rsi,%rdi
    af93:	e8 48 95 ff ff       	call   44e0 <__asan_report_load8@plt>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    af98:	bf 40 00 00 00       	mov    $0x40,%edi
    af9d:	e8 0e 98 ff ff       	call   47b0 <__asan_stack_malloc_0@plt>
    afa2:	48 85 c0             	test   %rax,%rax
    afa5:	48 0f 45 e8          	cmovne %rax,%rbp
    afa9:	e9 15 fe ff ff       	jmp    adc3 <handle_http_method+0x33>
    afae:	48 b8 f5 f5 f5 f5 f5 f5 f5 f5 	movabs $0xf5f5f5f5f5f5f5f5,%rax
    afb8:	48 c7 45 00 0e 36 e0 45 	movq   $0x45e0360e,0x0(%rbp)
    afc0:	48 89 83 00 80 ff 7f 	mov    %rax,0x7fff8000(%rbx)
    afc7:	48 8b 45 38          	mov    0x38(%rbp),%rax
    afcb:	c6 00 00             	movb   $0x0,(%rax)
    afce:	e9 72 ff ff ff       	jmp    af45 <handle_http_method+0x1b5>
}
    afd3:	e8 d8 96 ff ff       	call   46b0 <__stack_chk_fail@plt>
    afd8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

000000000000afe0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    afe0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    afe4:	85 d2                	test   %edx,%edx
    afe6:	0f 8e 9e 00 00 00    	jle    b08a <get_line+0xaa>
    afec:	48 63 d2             	movslq %edx,%rdx
int get_line(const char *src, char *dest, int dest_sz) {
    afef:	48 83 ec 08          	sub    $0x8,%rsp
    aff3:	4c 8d 04 17          	lea    (%rdi,%rdx,1),%r8
    aff7:	eb 13                	jmp    b00c <get_line+0x2c>
    aff9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int i = 0; i < dest_sz; i++) {
    b000:	48 89 d7             	mov    %rdx,%rdi
    b003:	48 83 c6 01          	add    $0x1,%rsi
    b007:	4c 39 c2             	cmp    %r8,%rdx
    b00a:	74 74                	je     b080 <get_line+0xa0>
        dest[i] = src[i];
    b00c:	48 89 f8             	mov    %rdi,%rax
    b00f:	48 89 fa             	mov    %rdi,%rdx
    b012:	48 c1 e8 03          	shr    $0x3,%rax
    b016:	83 e2 07             	and    $0x7,%edx
    b019:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    b020:	38 d0                	cmp    %dl,%al
    b022:	7f 04                	jg     b028 <get_line+0x48>
    b024:	84 c0                	test   %al,%al
    b026:	75 68                	jne    b090 <get_line+0xb0>
    b028:	48 89 f2             	mov    %rsi,%rdx
    b02b:	48 89 f1             	mov    %rsi,%rcx
    b02e:	0f b6 07             	movzbl (%rdi),%eax
    b031:	48 c1 ea 03          	shr    $0x3,%rdx
    b035:	83 e1 07             	and    $0x7,%ecx
    b038:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    b03f:	38 ca                	cmp    %cl,%dl
    b041:	7f 04                	jg     b047 <get_line+0x67>
    b043:	84 d2                	test   %dl,%dl
    b045:	75 4e                	jne    b095 <get_line+0xb5>
    b047:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    b049:	48 8d 57 01          	lea    0x1(%rdi),%rdx
    b04d:	3c 0d                	cmp    $0xd,%al
    b04f:	75 af                	jne    b000 <get_line+0x20>
    b051:	48 89 d0             	mov    %rdx,%rax
    b054:	48 89 d1             	mov    %rdx,%rcx
    b057:	48 c1 e8 03          	shr    $0x3,%rax
    b05b:	83 e1 07             	and    $0x7,%ecx
    b05e:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    b065:	38 c8                	cmp    %cl,%al
    b067:	7f 04                	jg     b06d <get_line+0x8d>
    b069:	84 c0                	test   %al,%al
    b06b:	75 30                	jne    b09d <get_line+0xbd>
    b06d:	80 7f 01 0a          	cmpb   $0xa,0x1(%rdi)
    b071:	75 8d                	jne    b000 <get_line+0x20>
            dest[i] = '\0';
    b073:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    b076:	31 c0                	xor    %eax,%eax
}
    b078:	48 83 c4 08          	add    $0x8,%rsp
    b07c:	c3                   	ret
    b07d:	0f 1f 00             	nopl   (%rax)
    return 1;
    b080:	b8 01 00 00 00       	mov    $0x1,%eax
}
    b085:	48 83 c4 08          	add    $0x8,%rsp
    b089:	c3                   	ret
    return 1;
    b08a:	b8 01 00 00 00       	mov    $0x1,%eax
}
    b08f:	c3                   	ret
        dest[i] = src[i];
    b090:	e8 fb 96 ff ff       	call   4790 <__asan_report_load1@plt>
    b095:	48 89 f7             	mov    %rsi,%rdi
    b098:	e8 33 97 ff ff       	call   47d0 <__asan_report_store1@plt>
        if (src[i] == '\r' && src[i+1] == '\n') {
    b09d:	48 89 d7             	mov    %rdx,%rdi
    b0a0:	e8 eb 96 ff ff       	call   4790 <__asan_report_load1@plt>
    b0a5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

000000000000b0b0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    b0b0:	f3 0f 1e fa          	endbr64
    b0b4:	41 56                	push   %r14
    b0b6:	49 89 f6             	mov    %rsi,%r14
    b0b9:	41 55                	push   %r13
    b0bb:	49 89 fd             	mov    %rdi,%r13
    b0be:	41 54                	push   %r12
    b0c0:	55                   	push   %rbp
    b0c1:	53                   	push   %rbx
    b0c2:	48 81 ec c0 04 00 00 	sub    $0x4c0,%rsp
    b0c9:	8b 05 b1 aa 00 00    	mov    0xaab1(%rip),%eax        # 15b80 <__asan_option_detect_stack_use_after_return@@Base>
    b0cf:	48 89 e3             	mov    %rsp,%rbx
    b0d2:	49 89 dc             	mov    %rbx,%r12
    b0d5:	85 c0                	test   %eax,%eax
    b0d7:	0f 85 12 02 00 00    	jne    b2ef <handle_client_request+0x23f>
    b0dd:	48 8d 05 52 70 00 00 	lea    0x7052(%rip),%rax        # 12136 <_IO_stdin_used+0x2136>
    b0e4:	48 89 dd             	mov    %rbx,%rbp
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
    b0e7:	49 8d 7d 10          	lea    0x10(%r13),%rdi
int handle_client_request(struct Request *req, struct io_uring *ring) {
    b0eb:	48 c7 03 b3 8a b5 41 	movq   $0x41b58ab3,(%rbx)
    b0f2:	48 89 43 08          	mov    %rax,0x8(%rbx)
    b0f6:	48 c1 ed 03          	shr    $0x3,%rbp
    b0fa:	48 8d 05 af ff ff ff 	lea    -0x51(%rip),%rax        # b0b0 <handle_client_request>
    b101:	4c 8d 8b c0 04 00 00 	lea    0x4c0(%rbx),%r9
    b108:	48 89 43 10          	mov    %rax,0x10(%rbx)
    b10c:	c7 85 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%rbp)
    b116:	c7 85 84 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff8084(%rbp)
    b120:	c7 85 88 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff8088(%rbp)
    b12a:	c7 85 8c 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff808c(%rbp)
    b134:	c7 85 90 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff8090(%rbp)
    b13e:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    b147:	48 89 84 24 b8 04 00 00 	mov    %rax,0x4b8(%rsp)
    b14f:	31 c0                	xor    %eax,%eax
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
    b151:	48 89 f8             	mov    %rdi,%rax
    b154:	48 c1 e8 03          	shr    $0x3,%rax
    b158:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    b15f:	0f 85 80 01 00 00    	jne    b2e5 <handle_client_request+0x235>
    for (int i = 0; i < dest_sz; i++) {
    b165:	49 8b 45 10          	mov    0x10(%r13),%rax
    b169:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
    b16d:	4c 8d 83 20 04 00 00 	lea    0x420(%rbx),%r8
    b174:	eb 1a                	jmp    b190 <handle_client_request+0xe0>
    b176:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    b180:	48 83 c7 01          	add    $0x1,%rdi
    b184:	48 89 c8             	mov    %rcx,%rax
    b187:	4c 39 c7             	cmp    %r8,%rdi
    b18a:	0f 84 f8 00 00 00    	je     b288 <handle_client_request+0x1d8>
        dest[i] = src[i];
    b190:	48 89 c2             	mov    %rax,%rdx
    b193:	48 89 c1             	mov    %rax,%rcx
    b196:	48 c1 ea 03          	shr    $0x3,%rdx
    b19a:	83 e1 07             	and    $0x7,%ecx
    b19d:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    b1a4:	38 ca                	cmp    %cl,%dl
    b1a6:	7f 08                	jg     b1b0 <handle_client_request+0x100>
    b1a8:	84 d2                	test   %dl,%dl
    b1aa:	0f 85 1b 01 00 00    	jne    b2cb <handle_client_request+0x21b>
    b1b0:	48 89 f9             	mov    %rdi,%rcx
    b1b3:	48 89 fe             	mov    %rdi,%rsi
    b1b6:	0f b6 10             	movzbl (%rax),%edx
    b1b9:	48 c1 e9 03          	shr    $0x3,%rcx
    b1bd:	83 e6 07             	and    $0x7,%esi
    b1c0:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    b1c7:	40 38 f1             	cmp    %sil,%cl
    b1ca:	7f 08                	jg     b1d4 <handle_client_request+0x124>
    b1cc:	84 c9                	test   %cl,%cl
    b1ce:	0f 85 ff 00 00 00    	jne    b2d3 <handle_client_request+0x223>
    b1d4:	88 17                	mov    %dl,(%rdi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    b1d6:	48 8d 48 01          	lea    0x1(%rax),%rcx
    b1da:	80 fa 0d             	cmp    $0xd,%dl
    b1dd:	75 a1                	jne    b180 <handle_client_request+0xd0>
    b1df:	48 89 ca             	mov    %rcx,%rdx
    b1e2:	48 89 ce             	mov    %rcx,%rsi
    b1e5:	48 c1 ea 03          	shr    $0x3,%rdx
    b1e9:	83 e6 07             	and    $0x7,%esi
    b1ec:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    b1f3:	40 38 f2             	cmp    %sil,%dl
    b1f6:	7f 08                	jg     b200 <handle_client_request+0x150>
    b1f8:	84 d2                	test   %dl,%dl
    b1fa:	0f 85 d8 00 00 00    	jne    b2d8 <handle_client_request+0x228>
    b200:	80 78 01 0a          	cmpb   $0xa,0x1(%rax)
    b204:	0f 85 76 ff ff ff    	jne    b180 <handle_client_request+0xd0>
            dest[i] = '\0';
    b20a:	c6 07 00             	movb   $0x0,(%rdi)
    handle_http_method(http_request, req->client_socket, ring);
    b20d:	49 8d 7d 08          	lea    0x8(%r13),%rdi
    b211:	48 89 f8             	mov    %rdi,%rax
    b214:	48 c1 e8 03          	shr    $0x3,%rax
    b218:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    b21f:	84 c0                	test   %al,%al
    b221:	74 08                	je     b22b <handle_client_request+0x17b>
    b223:	3c 03                	cmp    $0x3,%al
    b225:	0f 8e bf 00 00 00    	jle    b2ea <handle_client_request+0x23a>
    b22b:	41 8b 75 08          	mov    0x8(%r13),%esi
    b22f:	49 8d b9 60 fb ff ff 	lea    -0x4a0(%r9),%rdi
    b236:	4c 89 f2             	mov    %r14,%rdx
    b239:	e8 52 fb ff ff       	call   ad90 <handle_http_method>
int handle_client_request(struct Request *req, struct io_uring *ring) {
    b23e:	49 39 dc             	cmp    %rbx,%r12
    b241:	0f 85 c3 00 00 00    	jne    b30a <handle_client_request+0x25a>
    b247:	c7 85 00 80 ff 7f 00 00 00 00 	movl   $0x0,0x7fff8000(%rbp)
    b251:	66 0f ef c0          	pxor   %xmm0,%xmm0
    b255:	0f 11 85 84 80 ff 7f 	movups %xmm0,0x7fff8084(%rbp)
}
    b25c:	48 8b 84 24 b8 04 00 00 	mov    0x4b8(%rsp),%rax
    b264:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    b26d:	75 71                	jne    b2e0 <handle_client_request+0x230>
    b26f:	48 81 c4 c0 04 00 00 	add    $0x4c0,%rsp
    b276:	31 c0                	xor    %eax,%eax
    b278:	5b                   	pop    %rbx
    b279:	5d                   	pop    %rbp
    b27a:	41 5c                	pop    %r12
    b27c:	41 5d                	pop    %r13
    b27e:	41 5e                	pop    %r14
    b280:	c3                   	ret
    b281:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        fprintf(stderr, "Malformed request\n");
    b288:	48 8d 3d 11 a9 00 00 	lea    0xa911(%rip),%rdi        # 15ba0 <stderr@GLIBC_2.2.5>
    b28f:	48 89 f8             	mov    %rdi,%rax
    b292:	48 c1 e8 03          	shr    $0x3,%rax
    b296:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    b29d:	75 66                	jne    b305 <handle_client_request+0x255>
    b29f:	48 8b 0d fa a8 00 00 	mov    0xa8fa(%rip),%rcx        # 15ba0 <stderr@GLIBC_2.2.5>
    b2a6:	ba 12 00 00 00       	mov    $0x12,%edx
    b2ab:	be 01 00 00 00       	mov    $0x1,%esi
    b2b0:	48 8d 3d a9 57 00 00 	lea    0x57a9(%rip),%rdi        # 10a60 <_IO_stdin_used+0xa60>
    b2b7:	e8 e4 91 ff ff       	call   44a0 <fwrite@plt>
        exit(1);
    b2bc:	e8 4f 93 ff ff       	call   4610 <__asan_handle_no_return@plt>
    b2c1:	bf 01 00 00 00       	mov    $0x1,%edi
    b2c6:	e8 45 92 ff ff       	call   4510 <exit@plt>
        dest[i] = src[i];
    b2cb:	48 89 c7             	mov    %rax,%rdi
    b2ce:	e8 bd 94 ff ff       	call   4790 <__asan_report_load1@plt>
    b2d3:	e8 f8 94 ff ff       	call   47d0 <__asan_report_store1@plt>
        if (src[i] == '\r' && src[i+1] == '\n') {
    b2d8:	48 89 cf             	mov    %rcx,%rdi
    b2db:	e8 b0 94 ff ff       	call   4790 <__asan_report_load1@plt>
}
    b2e0:	e8 cb 93 ff ff       	call   46b0 <__stack_chk_fail@plt>
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
    b2e5:	e8 f6 91 ff ff       	call   44e0 <__asan_report_load8@plt>
    handle_http_method(http_request, req->client_socket, ring);
    b2ea:	e8 61 92 ff ff       	call   4550 <__asan_report_load4@plt>
int handle_client_request(struct Request *req, struct io_uring *ring) {
    b2ef:	bf a0 04 00 00       	mov    $0x4a0,%edi
    b2f4:	e8 77 94 ff ff       	call   4770 <__asan_stack_malloc_5@plt>
    b2f9:	48 85 c0             	test   %rax,%rax
    b2fc:	48 0f 45 d8          	cmovne %rax,%rbx
    b300:	e9 d8 fd ff ff       	jmp    b0dd <handle_client_request+0x2d>
        fprintf(stderr, "Malformed request\n");
    b305:	e8 d6 91 ff ff       	call   44e0 <__asan_report_load8@plt>
int handle_client_request(struct Request *req, struct io_uring *ring) {
    b30a:	48 c7 03 0e 36 e0 45 	movq   $0x45e0360e,(%rbx)
    b311:	4c 89 e2             	mov    %r12,%rdx
    b314:	be a0 04 00 00       	mov    $0x4a0,%esi
    b319:	48 89 df             	mov    %rbx,%rdi
    b31c:	e8 5f 93 ff ff       	call   4680 <__asan_stack_free_5@plt>
    b321:	e9 36 ff ff ff       	jmp    b25c <handle_client_request+0x1ac>
    b326:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

000000000000b330 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    b330:	f3 0f 1e fa          	endbr64
    b334:	55                   	push   %rbp
    b335:	41 89 f8             	mov    %edi,%r8d
	unsigned int head, next = sq->sqe_tail + 1;
    b338:	48 8d 79 44          	lea    0x44(%rcx),%rdi
    b33c:	49 89 d1             	mov    %rdx,%r9
    b33f:	53                   	push   %rbx
    b340:	48 89 f8             	mov    %rdi,%rax
    b343:	48 89 cd             	mov    %rcx,%rbp
    b346:	48 c1 e8 03          	shr    $0x3,%rax
    b34a:	48 83 ec 08          	sub    $0x8,%rsp
    b34e:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    b355:	48 89 f8             	mov    %rdi,%rax
    b358:	83 e0 07             	and    $0x7,%eax
    b35b:	83 c0 03             	add    $0x3,%eax
    b35e:	38 d0                	cmp    %dl,%al
    b360:	7c 08                	jl     b36a <add_accept_request+0x3a>
    b362:	84 d2                	test   %dl,%dl
    b364:	0f 85 71 03 00 00    	jne    b6db <add_accept_request+0x3ab>
	if (ring->flags & IORING_SETUP_SQE128)
    b36a:	48 8d bd c0 00 00 00 	lea    0xc0(%rbp),%rdi
	unsigned int head, next = sq->sqe_tail + 1;
    b371:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    b374:	48 89 fa             	mov    %rdi,%rdx
    b377:	48 c1 ea 03          	shr    $0x3,%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    b37b:	83 c0 01             	add    $0x1,%eax
	if (ring->flags & IORING_SETUP_SQE128)
    b37e:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    b385:	84 d2                	test   %dl,%dl
    b387:	74 09                	je     b392 <add_accept_request+0x62>
    b389:	80 fa 03             	cmp    $0x3,%dl
    b38c:	0f 8e 44 03 00 00    	jle    b6d6 <add_accept_request+0x3a6>
    b392:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    b398:	48 89 ef             	mov    %rbp,%rdi
    b39b:	48 c1 ef 03          	shr    $0x3,%rdi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    b39f:	89 ca                	mov    %ecx,%edx
    b3a1:	83 e2 02             	and    $0x2,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    b3a4:	80 bf 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdi)
    b3ab:	0f 85 7e 03 00 00    	jne    b72f <add_accept_request+0x3ff>
    b3b1:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    b3b5:	85 d2                	test   %edx,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    b3b7:	48 89 fa             	mov    %rdi,%rdx
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    b3ba:	0f 85 f0 02 00 00    	jne    b6b0 <add_accept_request+0x380>
		head = IO_URING_READ_ONCE(*sq->khead);
    b3c0:	48 c1 ea 03          	shr    $0x3,%rdx
    b3c4:	44 0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%r10d
    b3cc:	48 89 fa             	mov    %rdi,%rdx
    b3cf:	83 e2 07             	and    $0x7,%edx
    b3d2:	83 c2 03             	add    $0x3,%edx
    b3d5:	44 38 d2             	cmp    %r10b,%dl
    b3d8:	7c 09                	jl     b3e3 <add_accept_request+0xb3>
    b3da:	45 84 d2             	test   %r10b,%r10b
    b3dd:	0f 85 47 03 00 00    	jne    b72a <add_accept_request+0x3fa>
    b3e3:	8b 17                	mov    (%rdi),%edx
	if (next - head <= sq->ring_entries) {
    b3e5:	48 8d 7d 5c          	lea    0x5c(%rbp),%rdi
    b3e9:	41 89 c3             	mov    %eax,%r11d
    b3ec:	41 29 d3             	sub    %edx,%r11d
    b3ef:	48 89 fa             	mov    %rdi,%rdx
    b3f2:	48 c1 ea 03          	shr    $0x3,%rdx
    b3f6:	44 0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%r10d
    b3fe:	48 89 fa             	mov    %rdi,%rdx
    b401:	83 e2 07             	and    $0x7,%edx
    b404:	83 c2 03             	add    $0x3,%edx
    b407:	44 38 d2             	cmp    %r10b,%dl
    b40a:	7c 09                	jl     b415 <add_accept_request+0xe5>
    b40c:	45 84 d2             	test   %r10b,%r10b
    b40f:	0f 85 cb 02 00 00    	jne    b6e0 <add_accept_request+0x3b0>
    b415:	44 39 5d 5c          	cmp    %r11d,0x5c(%rbp)
    b419:	0f 82 94 95 ff ff    	jb     49b3 <add_accept_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    b41f:	48 8d 7d 38          	lea    0x38(%rbp),%rdi
    b423:	48 89 fa             	mov    %rdi,%rdx
    b426:	48 c1 ea 03          	shr    $0x3,%rdx
    b42a:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    b431:	0f 85 19 03 00 00    	jne    b750 <add_accept_request+0x420>
    b437:	4c 8d 55 58          	lea    0x58(%rbp),%r10
    b43b:	48 8b 5d 38          	mov    0x38(%rbp),%rbx
    b43f:	8b 55 44             	mov    0x44(%rbp),%edx
    b442:	4c 89 d7             	mov    %r10,%rdi
    b445:	48 c1 ef 03          	shr    $0x3,%rdi
    b449:	0f b6 bf 00 80 ff 7f 	movzbl 0x7fff8000(%rdi),%edi
    b450:	40 84 ff             	test   %dil,%dil
    b453:	74 0a                	je     b45f <add_accept_request+0x12f>
    b455:	40 80 ff 03          	cmp    $0x3,%dil
    b459:	0f 8e 98 02 00 00    	jle    b6f7 <add_accept_request+0x3c7>
	if (ring->flags & IORING_SETUP_SQE128)
    b45f:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    b462:	23 55 58             	and    0x58(%rbp),%edx
		sq->sqe_tail = next;
    b465:	89 45 44             	mov    %eax,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    b468:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    b46b:	d3 e2                	shl    %cl,%edx
    b46d:	48 c1 e2 06          	shl    $0x6,%rdx
    b471:	48 01 d3             	add    %rdx,%rbx
	sqe->opcode = (__u8) op;
    b474:	48 89 d8             	mov    %rbx,%rax
    b477:	48 c1 e8 03          	shr    $0x3,%rax
    b47b:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    b482:	84 c0                	test   %al,%al
    b484:	74 06                	je     b48c <add_accept_request+0x15c>
    b486:	0f 8e 5e 02 00 00    	jle    b6ea <add_accept_request+0x3ba>
	sqe->flags = 0;
    b48c:	48 8d 7b 01          	lea    0x1(%rbx),%rdi
	sqe->opcode = (__u8) op;
    b490:	c6 03 0d             	movb   $0xd,(%rbx)
	sqe->flags = 0;
    b493:	48 89 f8             	mov    %rdi,%rax
    b496:	48 89 fa             	mov    %rdi,%rdx
    b499:	48 c1 e8 03          	shr    $0x3,%rax
    b49d:	83 e2 07             	and    $0x7,%edx
    b4a0:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    b4a7:	38 d0                	cmp    %dl,%al
    b4a9:	7f 08                	jg     b4b3 <add_accept_request+0x183>
    b4ab:	84 c0                	test   %al,%al
    b4ad:	0f 85 32 02 00 00    	jne    b6e5 <add_accept_request+0x3b5>
	sqe->ioprio = 0;
    b4b3:	48 8d 7b 02          	lea    0x2(%rbx),%rdi
	sqe->flags = 0;
    b4b7:	c6 43 01 00          	movb   $0x0,0x1(%rbx)
	sqe->ioprio = 0;
    b4bb:	48 89 f8             	mov    %rdi,%rax
    b4be:	48 c1 e8 03          	shr    $0x3,%rax
    b4c2:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    b4c9:	48 89 f8             	mov    %rdi,%rax
    b4cc:	83 e0 07             	and    $0x7,%eax
    b4cf:	83 c0 01             	add    $0x1,%eax
    b4d2:	38 d0                	cmp    %dl,%al
    b4d4:	7c 08                	jl     b4de <add_accept_request+0x1ae>
    b4d6:	84 d2                	test   %dl,%dl
    b4d8:	0f 85 26 02 00 00    	jne    b704 <add_accept_request+0x3d4>
	sqe->fd = fd;
    b4de:	48 8d 7b 04          	lea    0x4(%rbx),%rdi
	sqe->ioprio = 0;
    b4e2:	31 c9                	xor    %ecx,%ecx
	sqe->fd = fd;
    b4e4:	48 89 f8             	mov    %rdi,%rax
	sqe->ioprio = 0;
    b4e7:	66 89 4b 02          	mov    %cx,0x2(%rbx)
	sqe->fd = fd;
    b4eb:	48 c1 e8 03          	shr    $0x3,%rax
    b4ef:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    b4f6:	48 89 f8             	mov    %rdi,%rax
    b4f9:	83 e0 07             	and    $0x7,%eax
    b4fc:	83 c0 03             	add    $0x3,%eax
    b4ff:	38 d0                	cmp    %dl,%al
    b501:	7c 08                	jl     b50b <add_accept_request+0x1db>
    b503:	84 d2                	test   %dl,%dl
    b505:	0f 85 f4 01 00 00    	jne    b6ff <add_accept_request+0x3cf>
	sqe->off = offset;
    b50b:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
	sqe->fd = fd;
    b50f:	44 89 43 04          	mov    %r8d,0x4(%rbx)
	sqe->off = offset;
    b513:	48 89 f8             	mov    %rdi,%rax
    b516:	48 c1 e8 03          	shr    $0x3,%rax
    b51a:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    b521:	0f 85 24 02 00 00    	jne    b74b <add_accept_request+0x41b>
	sqe->addr = (unsigned long) addr;
    b527:	48 8d 7b 10          	lea    0x10(%rbx),%rdi
	sqe->off = offset;
    b52b:	4c 89 4b 08          	mov    %r9,0x8(%rbx)
	sqe->addr = (unsigned long) addr;
    b52f:	48 89 f8             	mov    %rdi,%rax
    b532:	48 c1 e8 03          	shr    $0x3,%rax
    b536:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    b53d:	0f 85 03 02 00 00    	jne    b746 <add_accept_request+0x416>
	sqe->len = len;
    b543:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
	sqe->addr = (unsigned long) addr;
    b547:	48 89 73 10          	mov    %rsi,0x10(%rbx)
	sqe->len = len;
    b54b:	48 89 f8             	mov    %rdi,%rax
    b54e:	48 c1 e8 03          	shr    $0x3,%rax
    b552:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    b559:	84 c0                	test   %al,%al
    b55b:	74 08                	je     b565 <add_accept_request+0x235>
    b55d:	3c 03                	cmp    $0x3,%al
    b55f:	0f 8e 8d 01 00 00    	jle    b6f2 <add_accept_request+0x3c2>
	sqe->buf_index = 0;
    b565:	48 8d 7b 28          	lea    0x28(%rbx),%rdi
	sqe->len = len;
    b569:	c7 43 18 00 00 00 00 	movl   $0x0,0x18(%rbx)
	sqe->buf_index = 0;
    b570:	48 89 f8             	mov    %rdi,%rax
    b573:	48 c1 e8 03          	shr    $0x3,%rax
    b577:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    b57e:	84 c0                	test   %al,%al
    b580:	74 08                	je     b58a <add_accept_request+0x25a>
    b582:	3c 01                	cmp    $0x1,%al
    b584:	0f 8e 96 01 00 00    	jle    b720 <add_accept_request+0x3f0>
	sqe->personality = 0;
    b58a:	48 8d 7b 2a          	lea    0x2a(%rbx),%rdi
	sqe->buf_index = 0;
    b58e:	31 d2                	xor    %edx,%edx
	sqe->personality = 0;
    b590:	48 89 f8             	mov    %rdi,%rax
	sqe->buf_index = 0;
    b593:	66 89 53 28          	mov    %dx,0x28(%rbx)
	sqe->personality = 0;
    b597:	48 c1 e8 03          	shr    $0x3,%rax
    b59b:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    b5a2:	48 89 f8             	mov    %rdi,%rax
    b5a5:	83 e0 07             	and    $0x7,%eax
    b5a8:	83 c0 01             	add    $0x1,%eax
    b5ab:	38 d0                	cmp    %dl,%al
    b5ad:	7c 08                	jl     b5b7 <add_accept_request+0x287>
    b5af:	84 d2                	test   %dl,%dl
    b5b1:	0f 85 64 01 00 00    	jne    b71b <add_accept_request+0x3eb>
    b5b7:	31 c0                	xor    %eax,%eax
	sqe->file_index = 0;
    b5b9:	48 8d 7b 2c          	lea    0x2c(%rbx),%rdi
	sqe->personality = 0;
    b5bd:	66 89 43 2a          	mov    %ax,0x2a(%rbx)
	sqe->file_index = 0;
    b5c1:	48 89 f8             	mov    %rdi,%rax
    b5c4:	48 c1 e8 03          	shr    $0x3,%rax
    b5c8:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    b5cf:	48 89 f8             	mov    %rdi,%rax
    b5d2:	83 e0 07             	and    $0x7,%eax
    b5d5:	83 c0 03             	add    $0x3,%eax
    b5d8:	38 d0                	cmp    %dl,%al
    b5da:	7c 08                	jl     b5e4 <add_accept_request+0x2b4>
    b5dc:	84 d2                	test   %dl,%dl
    b5de:	0f 85 32 01 00 00    	jne    b716 <add_accept_request+0x3e6>
	sqe->addr3 = 0;
    b5e4:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
	sqe->file_index = 0;
    b5e8:	c7 43 2c 00 00 00 00 	movl   $0x0,0x2c(%rbx)
	sqe->addr3 = 0;
    b5ef:	48 89 f8             	mov    %rdi,%rax
    b5f2:	48 c1 e8 03          	shr    $0x3,%rax
    b5f6:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    b5fd:	0f 85 3e 01 00 00    	jne    b741 <add_accept_request+0x411>
	sqe->__pad2[0] = 0;
    b603:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
	sqe->addr3 = 0;
    b607:	48 c7 43 30 00 00 00 00 	movq   $0x0,0x30(%rbx)
	sqe->__pad2[0] = 0;
    b60f:	48 89 f8             	mov    %rdi,%rax
    b612:	48 c1 e8 03          	shr    $0x3,%rax
    b616:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    b61d:	0f 85 19 01 00 00    	jne    b73c <add_accept_request+0x40c>
	sqe->accept_flags = (__u32) flags;
    b623:	48 8d 7b 1c          	lea    0x1c(%rbx),%rdi
	sqe->__pad2[0] = 0;
    b627:	48 c7 43 38 00 00 00 00 	movq   $0x0,0x38(%rbx)
	sqe->accept_flags = (__u32) flags;
    b62f:	48 89 f8             	mov    %rdi,%rax
    b632:	48 c1 e8 03          	shr    $0x3,%rax
    b636:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    b63d:	48 89 f8             	mov    %rdi,%rax
    b640:	83 e0 07             	and    $0x7,%eax
    b643:	83 c0 03             	add    $0x3,%eax
    b646:	38 d0                	cmp    %dl,%al
    b648:	7c 08                	jl     b652 <add_accept_request+0x322>
    b64a:	84 d2                	test   %dl,%dl
    b64c:	0f 85 bf 00 00 00    	jne    b711 <add_accept_request+0x3e1>
    b652:	c7 43 1c 00 00 00 00 	movl   $0x0,0x1c(%rbx)
  struct Request *req = malloc(sizeof(*req));
    b659:	bf 10 00 00 00       	mov    $0x10,%edi
    b65e:	e8 2d 8f ff ff       	call   4590 <malloc@plt>
  req->event_type = EVENT_TYPE_ACCEPT;
    b663:	48 89 c2             	mov    %rax,%rdx
    b666:	48 c1 ea 03          	shr    $0x3,%rdx
    b66a:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    b671:	84 d2                	test   %dl,%dl
    b673:	74 09                	je     b67e <add_accept_request+0x34e>
    b675:	80 fa 03             	cmp    $0x3,%dl
    b678:	0f 8e 8b 00 00 00    	jle    b709 <add_accept_request+0x3d9>
	sqe->user_data = (unsigned long) data;
    b67e:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
    b682:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    b688:	48 89 fa             	mov    %rdi,%rdx
    b68b:	48 c1 ea 03          	shr    $0x3,%rdx
    b68f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    b696:	0f 85 9b 00 00 00    	jne    b737 <add_accept_request+0x407>
    b69c:	48 89 43 20          	mov    %rax,0x20(%rbx)
}
    b6a0:	48 83 c4 08          	add    $0x8,%rsp
  io_uring_submit(ring);
    b6a4:	48 89 ef             	mov    %rbp,%rdi
}
    b6a7:	5b                   	pop    %rbx
    b6a8:	5d                   	pop    %rbp
  io_uring_submit(ring);
    b6a9:	e9 b2 8f ff ff       	jmp    4660 <io_uring_submit@plt>
    b6ae:	66 90                	xchg   %ax,%ax
		head = io_uring_smp_load_acquire(sq->khead);
    b6b0:	48 c1 ea 03          	shr    $0x3,%rdx
    b6b4:	44 0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%r10d
    b6bc:	48 89 fa             	mov    %rdi,%rdx
    b6bf:	83 e2 07             	and    $0x7,%edx
    b6c2:	83 c2 03             	add    $0x3,%edx
    b6c5:	44 38 d2             	cmp    %r10b,%dl
    b6c8:	7c 05                	jl     b6cf <add_accept_request+0x39f>
    b6ca:	45 84 d2             	test   %r10b,%r10b
    b6cd:	75 56                	jne    b725 <add_accept_request+0x3f5>
    b6cf:	8b 17                	mov    (%rdi),%edx
    b6d1:	e9 0f fd ff ff       	jmp    b3e5 <add_accept_request+0xb5>
	if (ring->flags & IORING_SETUP_SQE128)
    b6d6:	e8 75 8e ff ff       	call   4550 <__asan_report_load4@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    b6db:	e8 70 8e ff ff       	call   4550 <__asan_report_load4@plt>
	if (next - head <= sq->ring_entries) {
    b6e0:	e8 6b 8e ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->flags = 0;
    b6e5:	e8 e6 90 ff ff       	call   47d0 <__asan_report_store1@plt>
	sqe->opcode = (__u8) op;
    b6ea:	48 89 df             	mov    %rbx,%rdi
    b6ed:	e8 de 90 ff ff       	call   47d0 <__asan_report_store1@plt>
	sqe->len = len;
    b6f2:	e8 c9 8f ff ff       	call   46c0 <__asan_report_store4@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    b6f7:	4c 89 d7             	mov    %r10,%rdi
    b6fa:	e8 51 8e ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->fd = fd;
    b6ff:	e8 bc 8f ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->ioprio = 0;
    b704:	e8 f7 8d ff ff       	call   4500 <__asan_report_store2@plt>
  req->event_type = EVENT_TYPE_ACCEPT;
    b709:	48 89 c7             	mov    %rax,%rdi
    b70c:	e8 af 8f ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->accept_flags = (__u32) flags;
    b711:	e8 aa 8f ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->file_index = 0;
    b716:	e8 a5 8f ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->personality = 0;
    b71b:	e8 e0 8d ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->buf_index = 0;
    b720:	e8 db 8d ff ff       	call   4500 <__asan_report_store2@plt>
		head = io_uring_smp_load_acquire(sq->khead);
    b725:	e8 26 8e ff ff       	call   4550 <__asan_report_load4@plt>
		head = IO_URING_READ_ONCE(*sq->khead);
    b72a:	e8 21 8e ff ff       	call   4550 <__asan_report_load4@plt>
    b72f:	48 89 ef             	mov    %rbp,%rdi
    b732:	e8 a9 8d ff ff       	call   44e0 <__asan_report_load8@plt>
	sqe->user_data = (unsigned long) data;
    b737:	e8 94 8f ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->__pad2[0] = 0;
    b73c:	e8 8f 8f ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->addr3 = 0;
    b741:	e8 8a 8f ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->addr = (unsigned long) addr;
    b746:	e8 85 8f ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->off = offset;
    b74b:	e8 80 8f ff ff       	call   46d0 <__asan_report_store8@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    b750:	e8 8b 8d ff ff       	call   44e0 <__asan_report_load8@plt>
    b755:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

000000000000b760 <io_thread>:
void* io_thread(void *arg) {
    b760:	f3 0f 1e fa          	endbr64
    b764:	41 57                	push   %r15
    b766:	41 56                	push   %r14
    b768:	41 55                	push   %r13
    b76a:	41 54                	push   %r12
    b76c:	55                   	push   %rbp
    b76d:	53                   	push   %rbx
    b76e:	48 81 ec 18 07 00 00 	sub    $0x718,%rsp
    b775:	44 8b 3d 04 a4 00 00 	mov    0xa404(%rip),%r15d        # 15b80 <__asan_option_detect_stack_use_after_return@@Base>
    b77c:	48 8d 84 24 b0 00 00 00 	lea    0xb0(%rsp),%rax
    b784:	48 89 7c 24 18       	mov    %rdi,0x18(%rsp)
    b789:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    b78e:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
    b796:	45 85 ff             	test   %r15d,%r15d
    b799:	0f 85 77 17 00 00    	jne    cf16 <io_thread+0x17b6>
    b79f:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    b7a4:	48 8d 35 45 68 00 00 	lea    0x6845(%rip),%rsi        # 11ff0 <_IO_stdin_used+0x1ff0>
    b7ab:	48 89 c5             	mov    %rax,%rbp
    b7ae:	48 89 70 08          	mov    %rsi,0x8(%rax)
    b7b2:	48 8d 35 a7 ff ff ff 	lea    -0x59(%rip),%rsi        # b760 <io_thread>
    b7b9:	48 8d 98 60 06 00 00 	lea    0x660(%rax),%rbx
    b7c0:	48 c1 ed 03          	shr    $0x3,%rbp
    b7c4:	48 c7 00 b3 8a b5 41 	movq   $0x41b58ab3,(%rax)
    b7cb:	48 89 70 10          	mov    %rsi,0x10(%rax)
    b7cf:	c7 85 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%rbp)
    b7d9:	c7 85 04 80 ff 7f 04 f2 04 f2 	movl   $0xf204f204,0x7fff8004(%rbp)
    b7e3:	c7 85 08 80 ff 7f 00 f2 f2 f2 	movl   $0xf2f2f200,0x7fff8008(%rbp)
    b7ed:	c7 85 0c 80 ff 7f 00 00 f2 f2 	movl   $0xf2f20000,0x7fff800c(%rbp)
    b7f7:	c7 85 10 80 ff 7f 00 00 f2 f2 	movl   $0xf2f20000,0x7fff8010(%rbp)
    b801:	c7 85 2c 80 ff 7f 00 00 00 f2 	movl   $0xf2000000,0x7fff802c(%rbp)
    b80b:	c7 85 30 80 ff 7f f2 f2 f2 f2 	movl   $0xf2f2f2f2,0x7fff8030(%rbp)
    b815:	c7 85 34 80 ff 7f f2 f2 f2 f2 	movl   $0xf2f2f2f2,0x7fff8034(%rbp)
    b81f:	c7 85 b8 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff80b8(%rbp)
    b829:	c7 85 bc 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff80bc(%rbp)
    b833:	c7 85 c0 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff80c0(%rbp)
    b83d:	c7 85 c4 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff80c4(%rbp)
  struct io_uring ring = *data->ring;
    b847:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    b850:	48 89 84 24 08 07 00 00 	mov    %rax,0x708(%rsp)
    b858:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    b85d:	4c 8d 60 58          	lea    0x58(%rax),%r12
    b861:	4d 89 e5             	mov    %r12,%r13
    b864:	49 c1 ed 03          	shr    $0x3,%r13
    b868:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    b870:	0f 85 98 16 00 00    	jne    cf0e <io_thread+0x17ae>
    b876:	48 8b 74 24 58       	mov    0x58(%rsp),%rsi
    b87b:	48 8b 78 58          	mov    0x58(%rax),%rdi
    b87f:	48 8d 8e a0 00 00 00 	lea    0xa0(%rsi),%rcx
    b886:	48 89 c8             	mov    %rcx,%rax
    b889:	48 c1 e8 03          	shr    $0x3,%rax
    b88d:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    b894:	48 8d 86 77 01 00 00 	lea    0x177(%rsi),%rax
    b89b:	48 89 c6             	mov    %rax,%rsi
    b89e:	83 e0 07             	and    $0x7,%eax
    b8a1:	48 c1 ee 03          	shr    $0x3,%rsi
    b8a5:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    b8ac:	40 38 c6             	cmp    %al,%sil
    b8af:	41 0f 9e c0          	setle  %r8b
    b8b3:	40 84 f6             	test   %sil,%sil
    b8b6:	0f 95 c0             	setne  %al
    b8b9:	41 84 c0             	test   %al,%r8b
    b8bc:	0f 85 3f 16 00 00    	jne    cf01 <io_thread+0x17a1>
    b8c2:	84 d2                	test   %dl,%dl
    b8c4:	40 0f 95 c6          	setne  %sil
    b8c8:	0f 9e c0             	setle  %al
    b8cb:	40 84 c6             	test   %al,%sil
    b8ce:	0f 85 2d 16 00 00    	jne    cf01 <io_thread+0x17a1>
    b8d4:	48 89 f8             	mov    %rdi,%rax
    b8d7:	48 c1 e8 03          	shr    $0x3,%rax
    b8db:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    b8e2:	48 8d 87 d7 00 00 00 	lea    0xd7(%rdi),%rax
    b8e9:	48 89 c6             	mov    %rax,%rsi
    b8ec:	83 e0 07             	and    $0x7,%eax
    b8ef:	48 c1 ee 03          	shr    $0x3,%rsi
    b8f3:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    b8fa:	40 38 c6             	cmp    %al,%sil
    b8fd:	41 0f 9e c0          	setle  %r8b
    b901:	40 84 f6             	test   %sil,%sil
    b904:	0f 95 c0             	setne  %al
    b907:	41 84 c0             	test   %al,%r8b
    b90a:	0f 85 e7 15 00 00    	jne    cef7 <io_thread+0x1797>
    b910:	84 d2                	test   %dl,%dl
    b912:	40 0f 95 c6          	setne  %sil
    b916:	0f 9e c0             	setle  %al
    b919:	40 84 c6             	test   %al,%sil
    b91c:	0f 85 d5 15 00 00    	jne    cef7 <io_thread+0x1797>
    b922:	f3 0f 6f 0f          	movdqu (%rdi),%xmm1
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    b926:	31 d2                	xor    %edx,%edx
    b928:	48 89 ce             	mov    %rcx,%rsi
  struct io_uring ring = *data->ring;
    b92b:	0f 29 8b 40 fa ff ff 	movaps %xmm1,-0x5c0(%rbx)
    b932:	f3 0f 6f 57 10       	movdqu 0x10(%rdi),%xmm2
    b937:	0f 29 93 50 fa ff ff 	movaps %xmm2,-0x5b0(%rbx)
    b93e:	f3 0f 6f 5f 20       	movdqu 0x20(%rdi),%xmm3
    b943:	0f 29 9b 60 fa ff ff 	movaps %xmm3,-0x5a0(%rbx)
    b94a:	f3 0f 6f 67 30       	movdqu 0x30(%rdi),%xmm4
    b94f:	0f 29 a3 70 fa ff ff 	movaps %xmm4,-0x590(%rbx)
    b956:	f3 0f 6f 6f 40       	movdqu 0x40(%rdi),%xmm5
    b95b:	0f 29 ab 80 fa ff ff 	movaps %xmm5,-0x580(%rbx)
    b962:	f3 0f 6f 77 50       	movdqu 0x50(%rdi),%xmm6
    b967:	0f 29 b3 90 fa ff ff 	movaps %xmm6,-0x570(%rbx)
    b96e:	f3 0f 6f 7f 60       	movdqu 0x60(%rdi),%xmm7
    b973:	0f 29 bb a0 fa ff ff 	movaps %xmm7,-0x560(%rbx)
    b97a:	f3 0f 6f 47 70       	movdqu 0x70(%rdi),%xmm0
    b97f:	0f 29 83 b0 fa ff ff 	movaps %xmm0,-0x550(%rbx)
    b986:	f3 0f 6f 8f 80 00 00 00 	movdqu 0x80(%rdi),%xmm1
    b98e:	0f 29 8b c0 fa ff ff 	movaps %xmm1,-0x540(%rbx)
    b995:	f3 0f 6f 97 90 00 00 00 	movdqu 0x90(%rdi),%xmm2
    b99d:	0f 29 93 d0 fa ff ff 	movaps %xmm2,-0x530(%rbx)
    b9a4:	f3 0f 6f 9f a0 00 00 00 	movdqu 0xa0(%rdi),%xmm3
    b9ac:	0f 29 9b e0 fa ff ff 	movaps %xmm3,-0x520(%rbx)
    b9b3:	f3 0f 6f a7 b0 00 00 00 	movdqu 0xb0(%rdi),%xmm4
    b9bb:	0f 29 a3 f0 fa ff ff 	movaps %xmm4,-0x510(%rbx)
    b9c2:	f3 0f 6f af c0 00 00 00 	movdqu 0xc0(%rdi),%xmm5
    b9ca:	0f 29 ab 00 fb ff ff 	movaps %xmm5,-0x500(%rbx)
    b9d1:	48 8b 87 d0 00 00 00 	mov    0xd0(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    b9d8:	bf 00 01 00 00       	mov    $0x100,%edi
  struct io_uring ring = *data->ring;
    b9dd:	48 89 83 10 fb ff ff 	mov    %rax,-0x4f0(%rbx)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    b9e4:	e8 87 8a ff ff       	call   4470 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    b9e9:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    b9f1:	0f 85 f8 14 00 00    	jne    ceef <io_thread+0x178f>
    b9f7:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    b9fc:	31 f6                	xor    %esi,%esi
    b9fe:	48 8b 78 58          	mov    0x58(%rax),%rdi
    ba02:	e8 29 8c ff ff       	call   4630 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    ba07:	31 d2                	xor    %edx,%edx
    ba09:	be 01 00 00 00       	mov    $0x1,%esi
    ba0e:	bf 02 00 00 00       	mov    $0x2,%edi
    ba13:	e8 78 8c ff ff       	call   4690 <socket@plt>
    ba18:	89 44 24 44          	mov    %eax,0x44(%rsp)
  if (sock == -1)
    ba1c:	83 f8 ff             	cmp    $0xffffffff,%eax
    ba1f:	0f 84 28 90 ff ff    	je     4a4d <io_thread.cold+0x7b>
  int enable = 1;
    ba25:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    ba2a:	48 8d 78 20          	lea    0x20(%rax),%rdi
    ba2e:	48 89 f8             	mov    %rdi,%rax
    ba31:	48 c1 e8 03          	shr    $0x3,%rax
    ba35:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    ba3c:	84 c0                	test   %al,%al
    ba3e:	74 08                	je     ba48 <io_thread+0x2e8>
    ba40:	3c 03                	cmp    $0x3,%al
    ba42:	0f 8e 80 15 00 00    	jle    cfc8 <io_thread+0x1868>
  if (setsockopt(sock,
    ba48:	8b 7c 24 44          	mov    0x44(%rsp),%edi
    ba4c:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    ba52:	ba 02 00 00 00       	mov    $0x2,%edx
    ba57:	48 8d 8b c0 f9 ff ff 	lea    -0x640(%rbx),%rcx
  int enable = 1;
    ba5e:	c7 83 c0 f9 ff ff 01 00 00 00 	movl   $0x1,-0x640(%rbx)
  if (setsockopt(sock,
    ba68:	be 01 00 00 00       	mov    $0x1,%esi
    ba6d:	e8 4e 8b ff ff       	call   45c0 <setsockopt@plt>
    ba72:	85 c0                	test   %eax,%eax
    ba74:	0f 88 81 8f ff ff    	js     49fb <io_thread.cold+0x29>
  return __builtin___memset_chk (__dest, __ch, __len,
    ba7a:	4c 8d a3 00 fa ff ff 	lea    -0x600(%rbx),%r12
    ba81:	48 8d bb 04 fa ff ff 	lea    -0x5fc(%rbx),%rdi
    ba88:	ba 0c 00 00 00       	mov    $0xc,%edx
    ba8d:	31 f6                	xor    %esi,%esi
    ba8f:	e8 0c 8c ff ff       	call   46a0 <memset@plt>
  srv_addr.sin_family = AF_INET;
    ba94:	4c 89 e0             	mov    %r12,%rax
    ba97:	48 c1 e8 03          	shr    $0x3,%rax
    ba9b:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    baa2:	84 c0                	test   %al,%al
    baa4:	74 08                	je     baae <io_thread+0x34e>
    baa6:	3c 01                	cmp    $0x1,%al
    baa8:	0f 8e 3e 15 00 00    	jle    cfec <io_thread+0x188c>
  srv_addr.sin_port = htons(port);
    baae:	48 8d bb 02 fa ff ff 	lea    -0x5fe(%rbx),%rdi
  srv_addr.sin_family = AF_INET;
    bab5:	41 be 02 00 00 00    	mov    $0x2,%r14d
  srv_addr.sin_port = htons(port);
    babb:	48 89 f8             	mov    %rdi,%rax
  srv_addr.sin_family = AF_INET;
    babe:	66 44 89 b3 00 fa ff ff 	mov    %r14w,-0x600(%rbx)
  srv_addr.sin_port = htons(port);
    bac6:	48 c1 e8 03          	shr    $0x3,%rax
    baca:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    bad1:	48 89 f8             	mov    %rdi,%rax
    bad4:	83 e0 07             	and    $0x7,%eax
    bad7:	83 c0 01             	add    $0x1,%eax
    bada:	38 d0                	cmp    %dl,%al
    badc:	7c 08                	jl     bae6 <io_thread+0x386>
    bade:	84 d2                	test   %dl,%dl
    bae0:	0f 85 01 15 00 00    	jne    cfe7 <io_thread+0x1887>
  if (bind(sock,
    bae6:	8b 7c 24 44          	mov    0x44(%rsp),%edi
  srv_addr.sin_port = htons(port);
    baea:	41 bd 18 db ff ff    	mov    $0xffffdb18,%r13d
  if (bind(sock,
    baf0:	ba 10 00 00 00       	mov    $0x10,%edx
    baf5:	4c 89 e6             	mov    %r12,%rsi
  srv_addr.sin_port = htons(port);
    baf8:	66 44 89 ab 02 fa ff ff 	mov    %r13w,-0x5fe(%rbx)
  if (bind(sock,
    bb00:	e8 7b 8c ff ff       	call   4780 <bind@plt>
    bb05:	85 c0                	test   %eax,%eax
    bb07:	0f 88 17 8f ff ff    	js     4a24 <io_thread.cold+0x52>
  if (listen(sock, 10) < 0) {
    bb0d:	8b 7c 24 44          	mov    0x44(%rsp),%edi
    bb11:	be 0a 00 00 00       	mov    $0xa,%esi
    bb16:	e8 05 8b ff ff       	call   4620 <listen@plt>
    bb1b:	85 c0                	test   %eax,%eax
    bb1d:	0f 88 c7 8e ff ff    	js     49ea <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    bb23:	ba db 18 00 00       	mov    $0x18db,%edx
    bb28:	48 8d 35 71 50 00 00 	lea    0x5071(%rip),%rsi        # 10ba0 <_IO_stdin_used+0xba0>
    bb2f:	bf 01 00 00 00       	mov    $0x1,%edi
    bb34:	31 c0                	xor    %eax,%eax
    bb36:	e8 e5 89 ff ff       	call   4520 <__printf_chk@plt>
  socklen_t client_addr_len = sizeof(client_addr);
    bb3b:	48 8d 83 d0 f9 ff ff 	lea    -0x630(%rbx),%rax
    bb42:	48 89 84 24 80 00 00 00 	mov    %rax,0x80(%rsp)
    bb4a:	48 c1 e8 03          	shr    $0x3,%rax
    bb4e:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    bb55:	84 c0                	test   %al,%al
    bb57:	74 08                	je     bb61 <io_thread+0x401>
    bb59:	3c 03                	cmp    $0x3,%al
    bb5b:	0f 8e 5a 14 00 00    	jle    cfbb <io_thread+0x185b>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    bb61:	48 8d 83 20 fa ff ff 	lea    -0x5e0(%rbx),%rax
    bb68:	48 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%rdx
    bb70:	8b 7c 24 44          	mov    0x44(%rsp),%edi
    bb74:	48 8d 8b 40 fa ff ff 	lea    -0x5c0(%rbx),%rcx
    bb7b:	48 89 c6             	mov    %rax,%rsi
    bb7e:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    bb83:	c7 83 d0 f9 ff ff 10 00 00 00 	movl   $0x10,-0x630(%rbx)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    bb8d:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
    bb95:	e8 96 f7 ff ff       	call   b330 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    bb9a:	bf 01 00 00 00       	mov    $0x1,%edi
    bb9f:	be 10 00 00 00       	mov    $0x10,%esi
    bba4:	e8 b7 88 ff ff       	call   4460 <calloc@plt>
    void *buf = malloc(size);
    bba9:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    bbae:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    void *buf = malloc(size);
    bbb3:	e8 d8 89 ff ff       	call   4590 <malloc@plt>
    if (!buf) {
    bbb8:	48 85 c0             	test   %rax,%rax
    bbbb:	0f 84 b7 13 00 00    	je     cf78 <io_thread+0x1818>
  iov->iov_base = zh_malloc(10);
    bbc1:	48 8b 54 24 28       	mov    0x28(%rsp),%rdx
    bbc6:	48 c1 ea 03          	shr    $0x3,%rdx
    bbca:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    bbd1:	0f 85 97 13 00 00    	jne    cf6e <io_thread+0x180e>
    bbd7:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  iov->iov_len = 10;
    bbdc:	48 8d 7e 08          	lea    0x8(%rsi),%rdi
  iov->iov_base = zh_malloc(10);
    bbe0:	48 89 06             	mov    %rax,(%rsi)
  iov->iov_len = 10;
    bbe3:	48 89 f8             	mov    %rdi,%rax
    bbe6:	48 c1 e8 03          	shr    $0x3,%rax
    bbea:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    bbf1:	0f 85 72 13 00 00    	jne    cf69 <io_thread+0x1809>
    bbf7:	48 c7 46 08 0a 00 00 00 	movq   $0xa,0x8(%rsi)
	unsigned int head, next = sq->sqe_tail + 1;
    bbff:	48 8d b3 84 fa ff ff 	lea    -0x57c(%rbx),%rsi
    bc06:	48 89 f0             	mov    %rsi,%rax
    bc09:	48 89 74 24 48       	mov    %rsi,0x48(%rsp)
    bc0e:	48 c1 e8 03          	shr    $0x3,%rax
    bc12:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    bc19:	48 89 f0             	mov    %rsi,%rax
    bc1c:	83 e0 07             	and    $0x7,%eax
    bc1f:	83 c0 03             	add    $0x3,%eax
    bc22:	38 d0                	cmp    %dl,%al
    bc24:	7c 08                	jl     bc2e <io_thread+0x4ce>
    bc26:	84 d2                	test   %dl,%dl
    bc28:	0f 85 33 13 00 00    	jne    cf61 <io_thread+0x1801>
	if (ring->flags & IORING_SETUP_SQE128)
    bc2e:	48 8d b3 00 fb ff ff 	lea    -0x500(%rbx),%rsi
	unsigned int head, next = sq->sqe_tail + 1;
    bc35:	8b 83 84 fa ff ff    	mov    -0x57c(%rbx),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    bc3b:	48 89 f2             	mov    %rsi,%rdx
    bc3e:	48 89 74 24 10       	mov    %rsi,0x10(%rsp)
    bc43:	48 c1 ea 03          	shr    $0x3,%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    bc47:	83 c0 01             	add    $0x1,%eax
	if (ring->flags & IORING_SETUP_SQE128)
    bc4a:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    bc51:	84 d2                	test   %dl,%dl
    bc53:	74 09                	je     bc5e <io_thread+0x4fe>
    bc55:	80 fa 03             	cmp    $0x3,%dl
    bc58:	0f 8e 79 13 00 00    	jle    cfd7 <io_thread+0x1877>
    bc5e:	8b 8b 00 fb ff ff    	mov    -0x500(%rbx),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    bc64:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    bc69:	89 ca                	mov    %ecx,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    bc6b:	48 c1 ee 03          	shr    $0x3,%rsi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    bc6f:	83 e2 02             	and    $0x2,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    bc72:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    bc79:	0f 85 4e 13 00 00    	jne    cfcd <io_thread+0x186d>
    bc7f:	48 8b bb 40 fa ff ff 	mov    -0x5c0(%rbx),%rdi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    bc86:	85 d2                	test   %edx,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    bc88:	48 89 fa             	mov    %rdi,%rdx
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    bc8b:	0f 85 3f 0b 00 00    	jne    c7d0 <io_thread+0x1070>
		head = IO_URING_READ_ONCE(*sq->khead);
    bc91:	48 c1 ea 03          	shr    $0x3,%rdx
    bc95:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    bc9c:	48 89 fa             	mov    %rdi,%rdx
    bc9f:	83 e2 07             	and    $0x7,%edx
    bca2:	83 c2 03             	add    $0x3,%edx
    bca5:	40 38 f2             	cmp    %sil,%dl
    bca8:	7c 09                	jl     bcb3 <io_thread+0x553>
    bcaa:	40 84 f6             	test   %sil,%sil
    bcad:	0f 85 85 12 00 00    	jne    cf38 <io_thread+0x17d8>
    bcb3:	8b 17                	mov    (%rdi),%edx
	if (next - head <= sq->ring_entries) {
    bcb5:	4c 8d 93 9c fa ff ff 	lea    -0x564(%rbx),%r10
    bcbc:	89 c7                	mov    %eax,%edi
    bcbe:	29 d7                	sub    %edx,%edi
    bcc0:	4c 89 d2             	mov    %r10,%rdx
    bcc3:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    bcc8:	48 c1 ea 03          	shr    $0x3,%rdx
    bccc:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    bcd3:	4c 89 d2             	mov    %r10,%rdx
    bcd6:	83 e2 07             	and    $0x7,%edx
    bcd9:	83 c2 03             	add    $0x3,%edx
    bcdc:	40 38 f2             	cmp    %sil,%dl
    bcdf:	7c 09                	jl     bcea <io_thread+0x58a>
    bce1:	40 84 f6             	test   %sil,%sil
    bce4:	0f 85 53 12 00 00    	jne    cf3d <io_thread+0x17dd>
    bcea:	39 bb 9c fa ff ff    	cmp    %edi,-0x564(%rbx)
    bcf0:	0f 82 3f 8d ff ff    	jb     4a35 <io_thread.cold+0x63>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    bcf6:	48 8d b3 78 fa ff ff 	lea    -0x588(%rbx),%rsi
    bcfd:	48 89 f2             	mov    %rsi,%rdx
    bd00:	48 89 74 24 70       	mov    %rsi,0x70(%rsp)
    bd05:	48 c1 ea 03          	shr    $0x3,%rdx
    bd09:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    bd10:	0f 85 2f 12 00 00    	jne    cf45 <io_thread+0x17e5>
    bd16:	48 8d b3 98 fa ff ff 	lea    -0x568(%rbx),%rsi
    bd1d:	48 8b bb 78 fa ff ff 	mov    -0x588(%rbx),%rdi
    bd24:	8b 93 84 fa ff ff    	mov    -0x57c(%rbx),%edx
    bd2a:	48 89 74 24 78       	mov    %rsi,0x78(%rsp)
    bd2f:	48 c1 ee 03          	shr    $0x3,%rsi
    bd33:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    bd3a:	40 84 f6             	test   %sil,%sil
    bd3d:	74 0a                	je     bd49 <io_thread+0x5e9>
    bd3f:	40 80 fe 03          	cmp    $0x3,%sil
    bd43:	0f 8e 04 12 00 00    	jle    cf4d <io_thread+0x17ed>
		sq->sqe_tail = next;
    bd49:	89 83 84 fa ff ff    	mov    %eax,-0x57c(%rbx)
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    bd4f:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
	if (ring->flags & IORING_SETUP_SQE128)
    bd54:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    bd57:	23 93 98 fa ff ff    	and    -0x568(%rbx),%edx
	if (ring->flags & IORING_SETUP_SQE128)
    bd5d:	83 e1 01             	and    $0x1,%ecx
    bd60:	48 83 c0 60          	add    $0x60,%rax
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    bd64:	d3 e2                	shl    %cl,%edx
    bd66:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    bd6b:	48 c1 e8 03          	shr    $0x3,%rax
    bd6f:	48 c1 e2 06          	shl    $0x6,%rdx
    bd73:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    bd7a:	48 01 d7             	add    %rdx,%rdi
    bd7d:	84 c0                	test   %al,%al
    bd7f:	74 08                	je     bd89 <io_thread+0x629>
    bd81:	3c 03                	cmp    $0x3,%al
    bd83:	0f 8e ce 11 00 00    	jle    cf57 <io_thread+0x17f7>
    bd89:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    bd8e:	8b 70 60             	mov    0x60(%rax),%esi
	sqe->opcode = (__u8) op;
    bd91:	48 89 f8             	mov    %rdi,%rax
    bd94:	48 c1 e8 03          	shr    $0x3,%rax
    bd98:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    bd9f:	84 c0                	test   %al,%al
    bda1:	74 06                	je     bda9 <io_thread+0x649>
    bda3:	0f 8e 6a 12 00 00    	jle    d013 <io_thread+0x18b3>
	sqe->flags = 0;
    bda9:	48 8d 47 01          	lea    0x1(%rdi),%rax
	sqe->opcode = (__u8) op;
    bdad:	c6 07 01             	movb   $0x1,(%rdi)
	sqe->flags = 0;
    bdb0:	48 89 c2             	mov    %rax,%rdx
    bdb3:	48 89 c1             	mov    %rax,%rcx
    bdb6:	48 c1 ea 03          	shr    $0x3,%rdx
    bdba:	83 e1 07             	and    $0x7,%ecx
    bdbd:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    bdc4:	38 ca                	cmp    %cl,%dl
    bdc6:	7f 08                	jg     bdd0 <io_thread+0x670>
    bdc8:	84 d2                	test   %dl,%dl
    bdca:	0f 85 48 12 00 00    	jne    d018 <io_thread+0x18b8>
	sqe->ioprio = 0;
    bdd0:	48 8d 57 02          	lea    0x2(%rdi),%rdx
	sqe->flags = 0;
    bdd4:	c6 47 01 00          	movb   $0x0,0x1(%rdi)
	sqe->ioprio = 0;
    bdd8:	48 89 d0             	mov    %rdx,%rax
    bddb:	48 c1 e8 03          	shr    $0x3,%rax
    bddf:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    bde6:	48 89 d0             	mov    %rdx,%rax
    bde9:	83 e0 07             	and    $0x7,%eax
    bdec:	83 c0 01             	add    $0x1,%eax
    bdef:	38 c8                	cmp    %cl,%al
    bdf1:	7c 08                	jl     bdfb <io_thread+0x69b>
    bdf3:	84 c9                	test   %cl,%cl
    bdf5:	0f 85 25 12 00 00    	jne    d020 <io_thread+0x18c0>
	sqe->fd = fd;
    bdfb:	48 8d 57 04          	lea    0x4(%rdi),%rdx
	sqe->ioprio = 0;
    bdff:	45 31 db             	xor    %r11d,%r11d
	sqe->fd = fd;
    be02:	48 89 d0             	mov    %rdx,%rax
	sqe->ioprio = 0;
    be05:	66 44 89 5f 02       	mov    %r11w,0x2(%rdi)
	sqe->fd = fd;
    be0a:	48 c1 e8 03          	shr    $0x3,%rax
    be0e:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    be15:	48 89 d0             	mov    %rdx,%rax
    be18:	83 e0 07             	and    $0x7,%eax
    be1b:	83 c0 03             	add    $0x3,%eax
    be1e:	38 c8                	cmp    %cl,%al
    be20:	7c 08                	jl     be2a <io_thread+0x6ca>
    be22:	84 c9                	test   %cl,%cl
    be24:	0f 85 fe 11 00 00    	jne    d028 <io_thread+0x18c8>
	sqe->off = offset;
    be2a:	48 8d 47 08          	lea    0x8(%rdi),%rax
	sqe->fd = fd;
    be2e:	89 77 04             	mov    %esi,0x4(%rdi)
	sqe->off = offset;
    be31:	48 89 c2             	mov    %rax,%rdx
    be34:	48 c1 ea 03          	shr    $0x3,%rdx
    be38:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    be3f:	0f 85 eb 11 00 00    	jne    d030 <io_thread+0x18d0>
	sqe->addr = (unsigned long) addr;
    be45:	48 8d 47 10          	lea    0x10(%rdi),%rax
	sqe->off = offset;
    be49:	48 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%rdi)
	sqe->addr = (unsigned long) addr;
    be51:	48 89 c2             	mov    %rax,%rdx
    be54:	48 c1 ea 03          	shr    $0x3,%rdx
    be58:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    be5f:	0f 85 d3 11 00 00    	jne    d038 <io_thread+0x18d8>
    be65:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
	sqe->len = len;
    be6a:	48 8d 57 18          	lea    0x18(%rdi),%rdx
	sqe->addr = (unsigned long) addr;
    be6e:	48 89 47 10          	mov    %rax,0x10(%rdi)
	sqe->len = len;
    be72:	48 89 d0             	mov    %rdx,%rax
    be75:	48 c1 e8 03          	shr    $0x3,%rax
    be79:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    be80:	84 c0                	test   %al,%al
    be82:	74 08                	je     be8c <io_thread+0x72c>
    be84:	3c 03                	cmp    $0x3,%al
    be86:	0f 8e b4 11 00 00    	jle    d040 <io_thread+0x18e0>
	sqe->rw_flags = 0;
    be8c:	48 8d 57 1c          	lea    0x1c(%rdi),%rdx
	sqe->len = len;
    be90:	c7 47 18 01 00 00 00 	movl   $0x1,0x18(%rdi)
	sqe->rw_flags = 0;
    be97:	48 89 d0             	mov    %rdx,%rax
    be9a:	48 c1 e8 03          	shr    $0x3,%rax
    be9e:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    bea5:	48 89 d0             	mov    %rdx,%rax
    bea8:	83 e0 07             	and    $0x7,%eax
    beab:	83 c0 03             	add    $0x3,%eax
    beae:	38 c8                	cmp    %cl,%al
    beb0:	7c 08                	jl     beba <io_thread+0x75a>
    beb2:	84 c9                	test   %cl,%cl
    beb4:	0f 85 8e 11 00 00    	jne    d048 <io_thread+0x18e8>
	sqe->buf_index = 0;
    beba:	48 8d 57 28          	lea    0x28(%rdi),%rdx
	sqe->rw_flags = 0;
    bebe:	c7 47 1c 00 00 00 00 	movl   $0x0,0x1c(%rdi)
	sqe->buf_index = 0;
    bec5:	48 89 d0             	mov    %rdx,%rax
    bec8:	48 c1 e8 03          	shr    $0x3,%rax
    becc:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    bed3:	84 c0                	test   %al,%al
    bed5:	74 08                	je     bedf <io_thread+0x77f>
    bed7:	3c 01                	cmp    $0x1,%al
    bed9:	0f 8e 71 11 00 00    	jle    d050 <io_thread+0x18f0>
	sqe->personality = 0;
    bedf:	48 8d 57 2a          	lea    0x2a(%rdi),%rdx
	sqe->buf_index = 0;
    bee3:	45 31 d2             	xor    %r10d,%r10d
	sqe->personality = 0;
    bee6:	48 89 d0             	mov    %rdx,%rax
	sqe->buf_index = 0;
    bee9:	66 44 89 57 28       	mov    %r10w,0x28(%rdi)
	sqe->personality = 0;
    beee:	48 c1 e8 03          	shr    $0x3,%rax
    bef2:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    bef9:	48 89 d0             	mov    %rdx,%rax
    befc:	83 e0 07             	and    $0x7,%eax
    beff:	83 c0 01             	add    $0x1,%eax
    bf02:	38 c8                	cmp    %cl,%al
    bf04:	7c 08                	jl     bf0e <io_thread+0x7ae>
    bf06:	84 c9                	test   %cl,%cl
    bf08:	0f 85 4a 11 00 00    	jne    d058 <io_thread+0x18f8>
	sqe->file_index = 0;
    bf0e:	48 8d 57 2c          	lea    0x2c(%rdi),%rdx
	sqe->personality = 0;
    bf12:	45 31 c9             	xor    %r9d,%r9d
	sqe->file_index = 0;
    bf15:	48 89 d0             	mov    %rdx,%rax
	sqe->personality = 0;
    bf18:	66 44 89 4f 2a       	mov    %r9w,0x2a(%rdi)
	sqe->file_index = 0;
    bf1d:	48 c1 e8 03          	shr    $0x3,%rax
    bf21:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    bf28:	48 89 d0             	mov    %rdx,%rax
    bf2b:	83 e0 07             	and    $0x7,%eax
    bf2e:	83 c0 03             	add    $0x3,%eax
    bf31:	38 c8                	cmp    %cl,%al
    bf33:	7c 08                	jl     bf3d <io_thread+0x7dd>
    bf35:	84 c9                	test   %cl,%cl
    bf37:	0f 85 23 11 00 00    	jne    d060 <io_thread+0x1900>
	sqe->addr3 = 0;
    bf3d:	48 8d 47 30          	lea    0x30(%rdi),%rax
	sqe->file_index = 0;
    bf41:	c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%rdi)
	sqe->addr3 = 0;
    bf48:	48 89 c2             	mov    %rax,%rdx
    bf4b:	48 c1 ea 03          	shr    $0x3,%rdx
    bf4f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    bf56:	0f 85 0c 11 00 00    	jne    d068 <io_thread+0x1908>
	sqe->__pad2[0] = 0;
    bf5c:	48 8d 47 38          	lea    0x38(%rdi),%rax
	sqe->addr3 = 0;
    bf60:	48 c7 47 30 00 00 00 00 	movq   $0x0,0x30(%rdi)
	sqe->__pad2[0] = 0;
    bf68:	48 89 c2             	mov    %rax,%rdx
    bf6b:	48 c1 ea 03          	shr    $0x3,%rdx
    bf6f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    bf76:	0f 85 51 0f 00 00    	jne    cecd <io_thread+0x176d>
	sqe->user_data = (unsigned long) data;
    bf7c:	48 8d 47 20          	lea    0x20(%rdi),%rax
	sqe->__pad2[0] = 0;
    bf80:	48 c7 47 38 00 00 00 00 	movq   $0x0,0x38(%rdi)
	sqe->user_data = (unsigned long) data;
    bf88:	48 89 c2             	mov    %rax,%rdx
    bf8b:	48 c1 ea 03          	shr    $0x3,%rdx
    bf8f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    bf96:	0f 85 39 0f 00 00    	jne    ced5 <io_thread+0x1775>
    bf9c:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    bfa1:	48 89 47 20          	mov    %rax,0x20(%rdi)
  io_uring_submit(&ring);
    bfa5:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    bfaa:	e8 b1 86 ff ff       	call   4660 <io_uring_submit@plt>
  while (data->running == 1) {
    bfaf:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    bfb4:	48 8d 70 44          	lea    0x44(%rax),%rsi
    bfb8:	48 89 f0             	mov    %rsi,%rax
    bfbb:	48 89 74 24 68       	mov    %rsi,0x68(%rsp)
    bfc0:	48 c1 e8 03          	shr    $0x3,%rax
    bfc4:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    bfcb:	48 89 f0             	mov    %rsi,%rax
    bfce:	83 e0 07             	and    $0x7,%eax
    bfd1:	83 c0 03             	add    $0x3,%eax
    bfd4:	38 d0                	cmp    %dl,%al
    bfd6:	7c 08                	jl     bfe0 <io_thread+0x880>
    bfd8:	84 d2                	test   %dl,%dl
    bfda:	0f 85 2b 10 00 00    	jne    d00b <io_thread+0x18ab>
    bfe0:	48 8d 83 f0 fa ff ff 	lea    -0x510(%rbx),%rax
    bfe7:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
		unsigned head = *ring->cq.khead;
    bfec:	48 8d 83 a8 fa ff ff 	lea    -0x558(%rbx),%rax
    bff3:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    bff8:	48 c1 e8 03          	shr    $0x3,%rax
    bffc:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    c001:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    c006:	83 78 44 01          	cmpl   $0x1,0x44(%rax)
    c00a:	0f 85 20 07 00 00    	jne    c730 <io_thread+0xfd0>
    c010:	48 89 ac 24 a8 00 00 00 	mov    %rbp,0xa8(%rsp)
    c018:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    c020:	48 8d 3d b9 4b 00 00 	lea    0x4bb9(%rip),%rdi        # 10be0 <_IO_stdin_used+0xbe0>
    c027:	e8 d4 87 ff ff       	call   4800 <puts@plt>
	unsigned mask = ring->cq.ring_mask;
    c02c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    c031:	48 c1 e8 03          	shr    $0x3,%rax
    c035:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    c03c:	84 c0                	test   %al,%al
    c03e:	74 08                	je     c048 <io_thread+0x8e8>
    c040:	3c 03                	cmp    $0x3,%al
    c042:	0f 8e 41 0d 00 00    	jle    cd89 <io_thread+0x1629>
	if (ring->flags & IORING_SETUP_CQE32)
    c048:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
	unsigned mask = ring->cq.ring_mask;
    c04d:	44 8b bb f0 fa ff ff 	mov    -0x510(%rbx),%r15d
	if (ring->flags & IORING_SETUP_CQE32)
    c054:	48 c1 e8 03          	shr    $0x3,%rax
    c058:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    c05f:	84 c0                	test   %al,%al
    c061:	74 08                	je     c06b <io_thread+0x90b>
    c063:	3c 03                	cmp    $0x3,%al
    c065:	0f 8e 95 0c 00 00    	jle    cd00 <io_thread+0x15a0>
    c06b:	8b 8b 00 fb ff ff    	mov    -0x500(%rbx),%ecx
    c071:	4c 8d b3 b0 fa ff ff 	lea    -0x550(%rbx),%r14
		cqe = &ring->cq.cqes[(head & mask) << shift];
    c078:	4c 8d ab d8 fa ff ff 	lea    -0x528(%rbx),%r13
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    c07f:	48 8d b3 08 fb ff ff 	lea    -0x4f8(%rbx),%rsi
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    c086:	4d 89 f2             	mov    %r14,%r10
		cqe = &ring->cq.cqes[(head & mask) << shift];
    c089:	4d 89 ec             	mov    %r13,%r12
	if (ring->flags & IORING_SETUP_CQE32)
    c08c:	c1 e9 0b             	shr    $0xb,%ecx
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    c08f:	49 89 f3             	mov    %rsi,%r11
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    c092:	49 c1 ea 03          	shr    $0x3,%r10
		cqe = &ring->cq.cqes[(head & mask) << shift];
    c096:	49 c1 ec 03          	shr    $0x3,%r12
	if (ring->flags & IORING_SETUP_CQE32)
    c09a:	83 e1 01             	and    $0x1,%ecx
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    c09d:	49 c1 eb 03          	shr    $0x3,%r11
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    c0a1:	41 80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r10)
    c0a9:	0f 85 1a 0c 00 00    	jne    ccc9 <io_thread+0x1569>
    c0af:	48 8b bb b0 fa ff ff 	mov    -0x550(%rbx),%rdi
    c0b6:	48 89 f8             	mov    %rdi,%rax
    c0b9:	48 c1 e8 03          	shr    $0x3,%rax
    c0bd:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    c0c4:	48 89 f8             	mov    %rdi,%rax
    c0c7:	83 e0 07             	and    $0x7,%eax
    c0ca:	83 c0 03             	add    $0x3,%eax
    c0cd:	38 d0                	cmp    %dl,%al
    c0cf:	7c 08                	jl     c0d9 <io_thread+0x979>
    c0d1:	84 d2                	test   %dl,%dl
    c0d3:	0f 85 f8 0b 00 00    	jne    ccd1 <io_thread+0x1571>
    c0d9:	44 8b 07             	mov    (%rdi),%r8d
		unsigned head = *ring->cq.khead;
    c0dc:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    c0e1:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c0e8:	0f 85 e8 0b 00 00    	jne    ccd6 <io_thread+0x1576>
    c0ee:	48 8b 93 a8 fa ff ff 	mov    -0x558(%rbx),%rdx
    c0f5:	48 89 d0             	mov    %rdx,%rax
    c0f8:	48 c1 e8 03          	shr    $0x3,%rax
    c0fc:	0f b6 b8 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edi
    c103:	48 89 d0             	mov    %rdx,%rax
    c106:	83 e0 07             	and    $0x7,%eax
    c109:	83 c0 03             	add    $0x3,%eax
    c10c:	40 38 f8             	cmp    %dil,%al
    c10f:	7c 09                	jl     c11a <io_thread+0x9ba>
    c111:	40 84 ff             	test   %dil,%dil
    c114:	0f 85 c6 0b 00 00    	jne    cce0 <io_thread+0x1580>
    c11a:	8b 02                	mov    (%rdx),%eax
		if (!available)
    c11c:	41 39 c0             	cmp    %eax,%r8d
    c11f:	0f 84 96 00 00 00    	je     c1bb <io_thread+0xa5b>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    c125:	41 80 bc 24 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r12)
    c12e:	0f 85 b4 0b 00 00    	jne    cce8 <io_thread+0x1588>
    c134:	44 89 ff             	mov    %r15d,%edi
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    c137:	45 0f b6 83 00 80 ff 7f 	movzbl 0x7fff8000(%r11),%r8d
		cqe = &ring->cq.cqes[(head & mask) << shift];
    c13f:	21 c7                	and    %eax,%edi
    c141:	d3 e7                	shl    %cl,%edi
    c143:	48 c1 e7 04          	shl    $0x4,%rdi
    c147:	48 03 bb d8 fa ff ff 	add    -0x528(%rbx),%rdi
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    c14e:	45 84 c0             	test   %r8b,%r8b
    c151:	74 0a                	je     c15d <io_thread+0x9fd>
    c153:	41 80 f8 03          	cmp    $0x3,%r8b
    c157:	0f 8e 93 0b 00 00    	jle    ccf0 <io_thread+0x1590>
    c15d:	f6 83 09 fb ff ff 01 	testb  $0x1,-0x4f7(%rbx)
    c164:	0f 85 96 06 00 00    	jne    c800 <io_thread+0x10a0>
				cqe->user_data == LIBURING_UDATA_TIMEOUT) {
    c16a:	49 89 f8             	mov    %rdi,%r8
    c16d:	49 c1 e8 03          	shr    $0x3,%r8
    c171:	41 80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r8)
    c179:	0f 85 3d 0b 00 00    	jne    ccbc <io_thread+0x155c>
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    c17f:	48 83 3f ff          	cmpq   $0xffffffffffffffff,(%rdi)
    c183:	0f 85 77 0a 00 00    	jne    cc00 <io_thread+0x14a0>
			if (cqe->res < 0)
    c189:	4c 8d 47 08          	lea    0x8(%rdi),%r8
    c18d:	4d 89 c1             	mov    %r8,%r9
    c190:	49 c1 e9 03          	shr    $0x3,%r9
    c194:	45 0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%r9),%r9d
    c19c:	45 84 c9             	test   %r9b,%r9b
    c19f:	74 0a                	je     c1ab <io_thread+0xa4b>
    c1a1:	41 80 f9 03          	cmp    $0x3,%r9b
    c1a5:	0f 8e 16 0b 00 00    	jle    ccc1 <io_thread+0x1561>
    c1ab:	8b 7f 08             	mov    0x8(%rdi),%edi
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    c1ae:	83 c0 01             	add    $0x1,%eax
    c1b1:	89 02                	mov    %eax,(%rdx)
			if (!err)
    c1b3:	85 ff                	test   %edi,%edi
    c1b5:	0f 89 e6 fe ff ff    	jns    c0a1 <io_thread+0x941>
	*cqe_ptr = cqe;
    c1bb:	4c 8d bb e0 f9 ff ff 	lea    -0x620(%rbx),%r15
    c1c2:	4c 89 f8             	mov    %r15,%rax
    c1c5:	48 c1 e8 03          	shr    $0x3,%rax
    c1c9:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c1d0:	0f 85 09 0e 00 00    	jne    cfdf <io_thread+0x187f>
    c1d6:	48 c7 83 e0 f9 ff ff 00 00 00 00 	movq   $0x0,-0x620(%rbx)
	return err;
    c1e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    c1e8:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
      if (cqe->user_data == 1) {
    c1ed:	4d 89 fc             	mov    %r15,%r12
    c1f0:	45 31 c0             	xor    %r8d,%r8d
    c1f3:	31 d2                	xor    %edx,%edx
    c1f5:	b9 01 00 00 00       	mov    $0x1,%ecx
    c1fa:	4c 89 fe             	mov    %r15,%rsi
    c1fd:	49 c1 ec 03          	shr    $0x3,%r12
    c201:	e8 3a 85 ff ff       	call   4740 <__io_uring_get_cqe@plt>
    c206:	41 80 bc 24 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r12)
    c20f:	41 89 c5             	mov    %eax,%r13d
    c212:	0f 85 01 0c 00 00    	jne    ce19 <io_thread+0x16b9>
    c218:	48 8b bb e0 f9 ff ff 	mov    -0x620(%rbx),%rdi
    c21f:	48 89 f8             	mov    %rdi,%rax
    c222:	48 c1 e8 03          	shr    $0x3,%rax
    c226:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c22d:	0f 85 ee 0b 00 00    	jne    ce21 <io_thread+0x16c1>
    c233:	48 83 3f 01          	cmpq   $0x1,(%rdi)
    c237:	0f 84 f3 09 00 00    	je     cc30 <io_thread+0x14d0>
    c23d:	48 8d 3d 1c 4a 00 00 	lea    0x4a1c(%rip),%rdi        # 10c60 <_IO_stdin_used+0xc60>
    c244:	e8 b7 85 ff ff       	call   4800 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    c249:	41 80 bc 24 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r12)
    c252:	0f 85 ce 0b 00 00    	jne    ce26 <io_thread+0x16c6>
    c258:	48 8b bb e0 f9 ff ff 	mov    -0x620(%rbx),%rdi
    c25f:	48 89 f8             	mov    %rdi,%rax
    c262:	48 c1 e8 03          	shr    $0x3,%rax
    c266:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c26d:	0f 85 bb 0b 00 00    	jne    ce2e <io_thread+0x16ce>
    c273:	4c 8b 37             	mov    (%rdi),%r14
      if (ret < 0)
    c276:	45 85 ed             	test   %r13d,%r13d
    c279:	0f 88 94 87 ff ff    	js     4a13 <io_thread.cold+0x41>
      if (cqe->res < 0) {
    c27f:	48 8d 57 08          	lea    0x8(%rdi),%rdx
    c283:	48 89 d0             	mov    %rdx,%rax
    c286:	48 c1 e8 03          	shr    $0x3,%rax
    c28a:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    c291:	84 c0                	test   %al,%al
    c293:	74 08                	je     c29d <io_thread+0xb3d>
    c295:	3c 03                	cmp    $0x3,%al
    c297:	0f 8e f6 0a 00 00    	jle    cd93 <io_thread+0x1633>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    c29d:	4c 89 f2             	mov    %r14,%rdx
      if (cqe->res < 0) {
    c2a0:	8b 47 08             	mov    0x8(%rdi),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    c2a3:	48 c1 ea 03          	shr    $0x3,%rdx
    c2a7:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    c2ae:	84 d2                	test   %dl,%dl
    c2b0:	74 09                	je     c2bb <io_thread+0xb5b>
    c2b2:	80 fa 03             	cmp    $0x3,%dl
    c2b5:	0f 8e 57 0a 00 00    	jle    cd12 <io_thread+0x15b2>
    c2bb:	45 8b 26             	mov    (%r14),%r12d
      if (cqe->res < 0) {
    c2be:	85 c0                	test   %eax,%eax
    c2c0:	0f 88 54 0a 00 00    	js     cd1a <io_thread+0x15ba>
      switch (req->event_type) {
    c2c6:	41 83 fc 01          	cmp    $0x1,%r12d
    c2ca:	0f 84 38 07 00 00    	je     ca08 <io_thread+0x12a8>
    c2d0:	41 83 fc 02          	cmp    $0x2,%r12d
    c2d4:	0f 84 36 06 00 00    	je     c910 <io_thread+0x11b0>
    c2da:	45 85 e4             	test   %r12d,%r12d
    c2dd:	0f 85 ad 05 00 00    	jne    c890 <io_thread+0x1130>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    c2e3:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    c2e8:	48 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%rdx
    c2f0:	48 8b b4 24 90 00 00 00 	mov    0x90(%rsp),%rsi
    c2f8:	8b 7c 24 44          	mov    0x44(%rsp),%edi
    c2fc:	e8 2f f0 ff ff       	call   b330 <add_accept_request>
              add_read_request(cqe->res, &ring);
    c301:	4c 89 f8             	mov    %r15,%rax
    c304:	48 c1 e8 03          	shr    $0x3,%rax
    c308:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c30f:	0f 85 96 0a 00 00    	jne    cdab <io_thread+0x164b>
    c315:	48 8b 83 e0 f9 ff ff 	mov    -0x620(%rbx),%rax
    c31c:	48 8d 78 08          	lea    0x8(%rax),%rdi
    c320:	48 89 fa             	mov    %rdi,%rdx
    c323:	48 c1 ea 03          	shr    $0x3,%rdx
    c327:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    c32e:	84 d2                	test   %dl,%dl
    c330:	74 09                	je     c33b <io_thread+0xbdb>
    c332:	80 fa 03             	cmp    $0x3,%dl
    c335:	0f 8e 78 0a 00 00    	jle    cdb3 <io_thread+0x1653>
    c33b:	8b 78 08             	mov    0x8(%rax),%edi
    c33e:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    c343:	e8 48 db ff ff       	call   9e90 <add_read_request>
              free(req);
    c348:	4c 89 f7             	mov    %r14,%rdi
    c34b:	e8 50 84 ff ff       	call   47a0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    c350:	4c 89 f8             	mov    %r15,%rax
    c353:	48 c1 e8 03          	shr    $0x3,%rax
    c357:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c35e:	0f 85 61 0a 00 00    	jne    cdc5 <io_thread+0x1665>
    c364:	48 8b 83 e0 f9 ff ff 	mov    -0x620(%rbx),%rax
	if (cqe)
    c36b:	48 85 c0             	test   %rax,%rax
    c36e:	0f 85 1c 05 00 00    	jne    c890 <io_thread+0x1130>
	unsigned int head, next = sq->sqe_tail + 1;
    c374:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
    c379:	48 89 f0             	mov    %rsi,%rax
    c37c:	48 c1 e8 03          	shr    $0x3,%rax
    c380:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    c387:	48 89 f0             	mov    %rsi,%rax
    c38a:	83 e0 07             	and    $0x7,%eax
    c38d:	83 c0 03             	add    $0x3,%eax
    c390:	38 d0                	cmp    %dl,%al
    c392:	7c 08                	jl     c39c <io_thread+0xc3c>
    c394:	84 d2                	test   %dl,%dl
    c396:	0f 85 d1 09 00 00    	jne    cd6d <io_thread+0x160d>
	if (ring->flags & IORING_SETUP_SQE128)
    c39c:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    c3a1:	8b 83 84 fa ff ff    	mov    -0x57c(%rbx),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    c3a7:	48 c1 ea 03          	shr    $0x3,%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    c3ab:	83 c0 01             	add    $0x1,%eax
	if (ring->flags & IORING_SETUP_SQE128)
    c3ae:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    c3b5:	84 d2                	test   %dl,%dl
    c3b7:	74 09                	je     c3c2 <io_thread+0xc62>
    c3b9:	80 fa 03             	cmp    $0x3,%dl
    c3bc:	0f 8e b3 09 00 00    	jle    cd75 <io_thread+0x1615>
    c3c2:	8b 8b 00 fb ff ff    	mov    -0x500(%rbx),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    c3c8:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    c3cd:	89 ca                	mov    %ecx,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    c3cf:	48 c1 ee 03          	shr    $0x3,%rsi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    c3d3:	83 e2 02             	and    $0x2,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    c3d6:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    c3dd:	0f 85 9c 09 00 00    	jne    cd7f <io_thread+0x161f>
    c3e3:	48 8b bb 40 fa ff ff 	mov    -0x5c0(%rbx),%rdi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    c3ea:	85 d2                	test   %edx,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    c3ec:	48 89 fa             	mov    %rdi,%rdx
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    c3ef:	0f 85 eb 04 00 00    	jne    c8e0 <io_thread+0x1180>
		head = IO_URING_READ_ONCE(*sq->khead);
    c3f5:	48 c1 ea 03          	shr    $0x3,%rdx
    c3f9:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    c400:	48 89 fa             	mov    %rdi,%rdx
    c403:	83 e2 07             	and    $0x7,%edx
    c406:	83 c2 03             	add    $0x3,%edx
    c409:	40 38 f2             	cmp    %sil,%dl
    c40c:	7c 09                	jl     c417 <io_thread+0xcb7>
    c40e:	40 84 f6             	test   %sil,%sil
    c411:	0f 85 79 08 00 00    	jne    cc90 <io_thread+0x1530>
    c417:	8b 17                	mov    (%rdi),%edx
	if (next - head <= sq->ring_entries) {
    c419:	4c 8b 5c 24 50       	mov    0x50(%rsp),%r11
    c41e:	89 c7                	mov    %eax,%edi
    c420:	29 d7                	sub    %edx,%edi
    c422:	4c 89 da             	mov    %r11,%rdx
    c425:	48 c1 ea 03          	shr    $0x3,%rdx
    c429:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    c430:	4c 89 da             	mov    %r11,%rdx
    c433:	83 e2 07             	and    $0x7,%edx
    c436:	83 c2 03             	add    $0x3,%edx
    c439:	40 38 f2             	cmp    %sil,%dl
    c43c:	7c 09                	jl     c447 <io_thread+0xce7>
    c43e:	40 84 f6             	test   %sil,%sil
    c441:	0f 85 b1 08 00 00    	jne    ccf8 <io_thread+0x1598>
    c447:	39 bb 9c fa ff ff    	cmp    %edi,-0x564(%rbx)
    c44d:	0f 82 7f 85 ff ff    	jb     49d2 <io_thread.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    c453:	48 8b 54 24 70       	mov    0x70(%rsp),%rdx
    c458:	48 c1 ea 03          	shr    $0x3,%rdx
    c45c:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    c463:	0f 85 a6 09 00 00    	jne    ce0f <io_thread+0x16af>
    c469:	48 8b 74 24 78       	mov    0x78(%rsp),%rsi
    c46e:	48 8b 93 78 fa ff ff 	mov    -0x588(%rbx),%rdx
    c475:	8b bb 84 fa ff ff    	mov    -0x57c(%rbx),%edi
    c47b:	48 c1 ee 03          	shr    $0x3,%rsi
    c47f:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    c486:	40 84 f6             	test   %sil,%sil
    c489:	74 0a                	je     c495 <io_thread+0xd35>
    c48b:	40 80 fe 03          	cmp    $0x3,%sil
    c48f:	0f 8e 59 09 00 00    	jle    cdee <io_thread+0x168e>
		sq->sqe_tail = next;
    c495:	89 83 84 fa ff ff    	mov    %eax,-0x57c(%rbx)
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    c49b:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
	if (ring->flags & IORING_SETUP_SQE128)
    c4a0:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    c4a3:	23 bb 98 fa ff ff    	and    -0x568(%rbx),%edi
	if (ring->flags & IORING_SETUP_SQE128)
    c4a9:	83 e1 01             	and    $0x1,%ecx
    c4ac:	48 c1 e8 03          	shr    $0x3,%rax
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    c4b0:	d3 e7                	shl    %cl,%edi
    c4b2:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    c4b9:	48 c1 e7 06          	shl    $0x6,%rdi
    c4bd:	48 01 d7             	add    %rdx,%rdi
    c4c0:	84 c0                	test   %al,%al
    c4c2:	74 08                	je     c4cc <io_thread+0xd6c>
    c4c4:	3c 03                	cmp    $0x3,%al
    c4c6:	0f 8e 2c 09 00 00    	jle    cdf8 <io_thread+0x1698>
    c4cc:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    c4d1:	8b 48 60             	mov    0x60(%rax),%ecx
	sqe->opcode = (__u8) op;
    c4d4:	48 89 f8             	mov    %rdi,%rax
    c4d7:	48 c1 e8 03          	shr    $0x3,%rax
    c4db:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    c4e2:	84 c0                	test   %al,%al
    c4e4:	74 06                	je     c4ec <io_thread+0xd8c>
    c4e6:	0f 8e 16 09 00 00    	jle    ce02 <io_thread+0x16a2>
	sqe->flags = 0;
    c4ec:	48 8d 47 01          	lea    0x1(%rdi),%rax
	sqe->opcode = (__u8) op;
    c4f0:	c6 07 01             	movb   $0x1,(%rdi)
	sqe->flags = 0;
    c4f3:	48 89 c2             	mov    %rax,%rdx
    c4f6:	48 89 c6             	mov    %rax,%rsi
    c4f9:	48 c1 ea 03          	shr    $0x3,%rdx
    c4fd:	83 e6 07             	and    $0x7,%esi
    c500:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    c507:	40 38 f2             	cmp    %sil,%dl
    c50a:	7f 08                	jg     c514 <io_thread+0xdb4>
    c50c:	84 d2                	test   %dl,%dl
    c50e:	0f 85 f3 08 00 00    	jne    ce07 <io_thread+0x16a7>
	sqe->ioprio = 0;
    c514:	48 8d 57 02          	lea    0x2(%rdi),%rdx
	sqe->flags = 0;
    c518:	c6 47 01 00          	movb   $0x0,0x1(%rdi)
	sqe->ioprio = 0;
    c51c:	48 89 d0             	mov    %rdx,%rax
    c51f:	48 c1 e8 03          	shr    $0x3,%rax
    c523:	0f b6 b0 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%esi
    c52a:	48 89 d0             	mov    %rdx,%rax
    c52d:	83 e0 07             	and    $0x7,%eax
    c530:	83 c0 01             	add    $0x1,%eax
    c533:	40 38 f0             	cmp    %sil,%al
    c536:	7c 09                	jl     c541 <io_thread+0xde1>
    c538:	40 84 f6             	test   %sil,%sil
    c53b:	0f 85 f7 08 00 00    	jne    ce38 <io_thread+0x16d8>
	sqe->fd = fd;
    c541:	48 8d 57 04          	lea    0x4(%rdi),%rdx
	sqe->ioprio = 0;
    c545:	31 f6                	xor    %esi,%esi
	sqe->fd = fd;
    c547:	48 89 d0             	mov    %rdx,%rax
	sqe->ioprio = 0;
    c54a:	66 89 77 02          	mov    %si,0x2(%rdi)
	sqe->fd = fd;
    c54e:	48 c1 e8 03          	shr    $0x3,%rax
    c552:	0f b6 b0 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%esi
    c559:	48 89 d0             	mov    %rdx,%rax
    c55c:	83 e0 07             	and    $0x7,%eax
    c55f:	83 c0 03             	add    $0x3,%eax
    c562:	40 38 f0             	cmp    %sil,%al
    c565:	7c 09                	jl     c570 <io_thread+0xe10>
    c567:	40 84 f6             	test   %sil,%sil
    c56a:	0f 85 d0 08 00 00    	jne    ce40 <io_thread+0x16e0>
	sqe->off = offset;
    c570:	48 8d 47 08          	lea    0x8(%rdi),%rax
	sqe->fd = fd;
    c574:	89 4f 04             	mov    %ecx,0x4(%rdi)
	sqe->off = offset;
    c577:	48 89 c2             	mov    %rax,%rdx
    c57a:	48 c1 ea 03          	shr    $0x3,%rdx
    c57e:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    c585:	0f 85 bd 08 00 00    	jne    ce48 <io_thread+0x16e8>
	sqe->addr = (unsigned long) addr;
    c58b:	48 8d 47 10          	lea    0x10(%rdi),%rax
	sqe->off = offset;
    c58f:	48 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%rdi)
	sqe->addr = (unsigned long) addr;
    c597:	48 89 c2             	mov    %rax,%rdx
    c59a:	48 c1 ea 03          	shr    $0x3,%rdx
    c59e:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    c5a5:	0f 85 a5 08 00 00    	jne    ce50 <io_thread+0x16f0>
    c5ab:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
	sqe->len = len;
    c5b0:	48 8d 57 18          	lea    0x18(%rdi),%rdx
	sqe->addr = (unsigned long) addr;
    c5b4:	48 89 47 10          	mov    %rax,0x10(%rdi)
	sqe->len = len;
    c5b8:	48 89 d0             	mov    %rdx,%rax
    c5bb:	48 c1 e8 03          	shr    $0x3,%rax
    c5bf:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    c5c6:	84 c0                	test   %al,%al
    c5c8:	74 08                	je     c5d2 <io_thread+0xe72>
    c5ca:	3c 03                	cmp    $0x3,%al
    c5cc:	0f 8e 86 08 00 00    	jle    ce58 <io_thread+0x16f8>
	sqe->rw_flags = 0;
    c5d2:	48 8d 57 1c          	lea    0x1c(%rdi),%rdx
	sqe->len = len;
    c5d6:	c7 47 18 01 00 00 00 	movl   $0x1,0x18(%rdi)
	sqe->rw_flags = 0;
    c5dd:	48 89 d0             	mov    %rdx,%rax
    c5e0:	48 c1 e8 03          	shr    $0x3,%rax
    c5e4:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    c5eb:	48 89 d0             	mov    %rdx,%rax
    c5ee:	83 e0 07             	and    $0x7,%eax
    c5f1:	83 c0 03             	add    $0x3,%eax
    c5f4:	38 c8                	cmp    %cl,%al
    c5f6:	7c 08                	jl     c600 <io_thread+0xea0>
    c5f8:	84 c9                	test   %cl,%cl
    c5fa:	0f 85 60 08 00 00    	jne    ce60 <io_thread+0x1700>
	sqe->buf_index = 0;
    c600:	48 8d 57 28          	lea    0x28(%rdi),%rdx
	sqe->rw_flags = 0;
    c604:	c7 47 1c 00 00 00 00 	movl   $0x0,0x1c(%rdi)
	sqe->buf_index = 0;
    c60b:	48 89 d0             	mov    %rdx,%rax
    c60e:	48 c1 e8 03          	shr    $0x3,%rax
    c612:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    c619:	84 c0                	test   %al,%al
    c61b:	74 08                	je     c625 <io_thread+0xec5>
    c61d:	3c 01                	cmp    $0x1,%al
    c61f:	0f 8e 43 08 00 00    	jle    ce68 <io_thread+0x1708>
    c625:	31 d2                	xor    %edx,%edx
    c627:	66 89 57 28          	mov    %dx,0x28(%rdi)
	sqe->personality = 0;
    c62b:	48 8d 57 2a          	lea    0x2a(%rdi),%rdx
    c62f:	48 89 d0             	mov    %rdx,%rax
    c632:	48 c1 e8 03          	shr    $0x3,%rax
    c636:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    c63d:	48 89 d0             	mov    %rdx,%rax
    c640:	83 e0 07             	and    $0x7,%eax
    c643:	83 c0 01             	add    $0x1,%eax
    c646:	38 c8                	cmp    %cl,%al
    c648:	7c 08                	jl     c652 <io_thread+0xef2>
    c64a:	84 c9                	test   %cl,%cl
    c64c:	0f 85 1e 08 00 00    	jne    ce70 <io_thread+0x1710>
    c652:	31 c0                	xor    %eax,%eax
	sqe->file_index = 0;
    c654:	48 8d 57 2c          	lea    0x2c(%rdi),%rdx
	sqe->personality = 0;
    c658:	66 89 47 2a          	mov    %ax,0x2a(%rdi)
	sqe->file_index = 0;
    c65c:	48 89 d0             	mov    %rdx,%rax
    c65f:	48 c1 e8 03          	shr    $0x3,%rax
    c663:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    c66a:	48 89 d0             	mov    %rdx,%rax
    c66d:	83 e0 07             	and    $0x7,%eax
    c670:	83 c0 03             	add    $0x3,%eax
    c673:	38 c8                	cmp    %cl,%al
    c675:	7c 08                	jl     c67f <io_thread+0xf1f>
    c677:	84 c9                	test   %cl,%cl
    c679:	0f 85 f9 07 00 00    	jne    ce78 <io_thread+0x1718>
	sqe->addr3 = 0;
    c67f:	48 8d 47 30          	lea    0x30(%rdi),%rax
	sqe->file_index = 0;
    c683:	c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%rdi)
	sqe->addr3 = 0;
    c68a:	48 89 c2             	mov    %rax,%rdx
    c68d:	48 c1 ea 03          	shr    $0x3,%rdx
    c691:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    c698:	0f 85 e2 07 00 00    	jne    ce80 <io_thread+0x1720>
	sqe->__pad2[0] = 0;
    c69e:	48 8d 47 38          	lea    0x38(%rdi),%rax
	sqe->addr3 = 0;
    c6a2:	48 c7 47 30 00 00 00 00 	movq   $0x0,0x30(%rdi)
	sqe->__pad2[0] = 0;
    c6aa:	48 89 c2             	mov    %rax,%rdx
    c6ad:	48 c1 ea 03          	shr    $0x3,%rdx
    c6b1:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    c6b8:	0f 85 ca 07 00 00    	jne    ce88 <io_thread+0x1728>
	sqe->user_data = (unsigned long) data;
    c6be:	48 8d 47 20          	lea    0x20(%rdi),%rax
	sqe->__pad2[0] = 0;
    c6c2:	48 c7 47 38 00 00 00 00 	movq   $0x0,0x38(%rdi)
	sqe->user_data = (unsigned long) data;
    c6ca:	48 89 c2             	mov    %rax,%rdx
    c6cd:	48 c1 ea 03          	shr    $0x3,%rdx
    c6d1:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    c6d8:	0f 85 bd 06 00 00    	jne    cd9b <io_thread+0x163b>
    c6de:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    c6e3:	48 89 47 20          	mov    %rax,0x20(%rdi)
      io_uring_submit(&ring);
    c6e7:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    c6ec:	e8 6f 7f ff ff       	call   4660 <io_uring_submit@plt>
  while (data->running == 1) {
    c6f1:	48 8b 74 24 68       	mov    0x68(%rsp),%rsi
    c6f6:	48 89 f0             	mov    %rsi,%rax
    c6f9:	48 c1 e8 03          	shr    $0x3,%rax
    c6fd:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    c704:	48 89 f0             	mov    %rsi,%rax
    c707:	83 e0 07             	and    $0x7,%eax
    c70a:	83 c0 03             	add    $0x3,%eax
    c70d:	38 d0                	cmp    %dl,%al
    c70f:	7c 08                	jl     c719 <io_thread+0xfb9>
    c711:	84 d2                	test   %dl,%dl
    c713:	0f 85 8a 06 00 00    	jne    cda3 <io_thread+0x1643>
    c719:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    c71e:	83 78 44 01          	cmpl   $0x1,0x44(%rax)
    c722:	0f 84 f8 f8 ff ff    	je     c020 <io_thread+0x8c0>
    c728:	48 8b ac 24 a8 00 00 00 	mov    0xa8(%rsp),%rbp
    c730:	48 8d 3d 49 46 00 00 	lea    0x4649(%rip),%rdi        # 10d80 <_IO_stdin_used+0xd80>
    c737:	e8 c4 80 ff ff       	call   4800 <puts@plt>
void* io_thread(void *arg) {
    c73c:	48 8b 5c 24 58       	mov    0x58(%rsp),%rbx
    c741:	48 39 9c 24 98 00 00 00 	cmp    %rbx,0x98(%rsp)
    c749:	0f 85 53 07 00 00    	jne    cea2 <io_thread+0x1742>
    c74f:	48 8d bd 34 80 ff 7f 	lea    0x7fff8034(%rbp),%rdi
    c756:	66 0f ef c0          	pxor   %xmm0,%xmm0
    c75a:	48 8d 85 2c 80 ff 7f 	lea    0x7fff802c(%rbp),%rax
    c761:	c7 85 10 80 ff 7f 00 00 00 00 	movl   $0x0,0x7fff8010(%rbp)
    c76b:	48 83 e7 f8          	and    $0xfffffffffffffff8,%rdi
    c76f:	0f 11 85 00 80 ff 7f 	movups %xmm0,0x7fff8000(%rbp)
    c776:	48 c7 85 2c 80 ff 7f 00 00 00 00 	movq   $0x0,0x7fff802c(%rbp)
    c781:	48 29 f8             	sub    %rdi,%rax
    c784:	8d 88 9c 00 00 00    	lea    0x9c(%rax),%ecx
    c78a:	48 c7 85 c0 80 ff 7f 00 00 00 00 	movq   $0x0,0x7fff80c0(%rbp)
    c795:	89 c8                	mov    %ecx,%eax
    c797:	c1 e8 03             	shr    $0x3,%eax
    c79a:	89 c1                	mov    %eax,%ecx
    c79c:	31 c0                	xor    %eax,%eax
    c79e:	f3 48 ab             	rep stos %rax,%es:(%rdi)
}
    c7a1:	48 8b 84 24 08 07 00 00 	mov    0x708(%rsp),%rax
    c7a9:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    c7b2:	0f 85 10 07 00 00    	jne    cec8 <io_thread+0x1768>
    c7b8:	48 81 c4 18 07 00 00 	add    $0x718,%rsp
    c7bf:	31 c0                	xor    %eax,%eax
    c7c1:	5b                   	pop    %rbx
    c7c2:	5d                   	pop    %rbp
    c7c3:	41 5c                	pop    %r12
    c7c5:	41 5d                	pop    %r13
    c7c7:	41 5e                	pop    %r14
    c7c9:	41 5f                	pop    %r15
    c7cb:	c3                   	ret
    c7cc:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    c7d0:	48 c1 ea 03          	shr    $0x3,%rdx
    c7d4:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    c7db:	48 89 fa             	mov    %rdi,%rdx
    c7de:	83 e2 07             	and    $0x7,%edx
    c7e1:	83 c2 03             	add    $0x3,%edx
    c7e4:	40 38 f2             	cmp    %sil,%dl
    c7e7:	7c 09                	jl     c7f2 <io_thread+0x1092>
    c7e9:	40 84 f6             	test   %sil,%sil
    c7ec:	0f 85 41 07 00 00    	jne    cf33 <io_thread+0x17d3>
    c7f2:	8b 17                	mov    (%rdi),%edx
    c7f4:	e9 bc f4 ff ff       	jmp    bcb5 <io_thread+0x555>
    c7f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
	*cqe_ptr = cqe;
    c800:	4c 8d bb e0 f9 ff ff 	lea    -0x620(%rbx),%r15
    c807:	4c 89 f8             	mov    %r15,%rax
    c80a:	48 c1 e8 03          	shr    $0x3,%rax
    c80e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c815:	0f 85 ef 04 00 00    	jne    cd0a <io_thread+0x15aa>
    c81b:	48 89 bb e0 f9 ff ff 	mov    %rdi,-0x620(%rbx)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    c822:	48 85 ff             	test   %rdi,%rdi
    c825:	0f 84 bd f9 ff ff    	je     c1e8 <io_thread+0xa88>
      if (cqe->user_data == 1) {
    c82b:	48 89 f8             	mov    %rdi,%rax
    c82e:	48 c1 e8 03          	shr    $0x3,%rax
    c832:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c839:	0f 85 8e 05 00 00    	jne    cdcd <io_thread+0x166d>
    c83f:	48 83 3f 01          	cmpq   $0x1,(%rdi)
    c843:	0f 84 e7 03 00 00    	je     cc30 <io_thread+0x14d0>
    c849:	48 8d 3d 10 44 00 00 	lea    0x4410(%rip),%rdi        # 10c60 <_IO_stdin_used+0xc60>
    c850:	e8 ab 7f ff ff       	call   4800 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    c855:	4c 89 f8             	mov    %r15,%rax
    c858:	48 c1 e8 03          	shr    $0x3,%rax
    c85c:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c863:	0f 85 69 05 00 00    	jne    cdd2 <io_thread+0x1672>
    c869:	48 8b bb e0 f9 ff ff 	mov    -0x620(%rbx),%rdi
    c870:	48 89 f8             	mov    %rdi,%rax
    c873:	48 c1 e8 03          	shr    $0x3,%rax
    c877:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c87e:	0f 85 56 05 00 00    	jne    cdda <io_thread+0x167a>
    c884:	4c 8b 37             	mov    (%rdi),%r14
      if (ret < 0)
    c887:	e9 f3 f9 ff ff       	jmp    c27f <io_thread+0xb1f>
    c88c:	0f 1f 40 00          	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    c890:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    c895:	48 c1 e8 03          	shr    $0x3,%rax
    c899:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c8a0:	0f 85 39 05 00 00    	jne    cddf <io_thread+0x167f>
    c8a6:	48 8b bb a8 fa ff ff 	mov    -0x558(%rbx),%rdi
    c8ad:	48 89 f8             	mov    %rdi,%rax
    c8b0:	48 c1 e8 03          	shr    $0x3,%rax
    c8b4:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    c8bb:	48 89 f8             	mov    %rdi,%rax
    c8be:	83 e0 07             	and    $0x7,%eax
    c8c1:	83 c0 03             	add    $0x3,%eax
    c8c4:	38 d0                	cmp    %dl,%al
    c8c6:	7c 08                	jl     c8d0 <io_thread+0x1170>
    c8c8:	84 d2                	test   %dl,%dl
    c8ca:	0f 85 19 05 00 00    	jne    cde9 <io_thread+0x1689>
    c8d0:	8b 07                	mov    (%rdi),%eax
    c8d2:	83 c0 01             	add    $0x1,%eax
    c8d5:	89 07                	mov    %eax,(%rdi)
}
    c8d7:	e9 98 fa ff ff       	jmp    c374 <io_thread+0xc14>
    c8dc:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    c8e0:	48 c1 ea 03          	shr    $0x3,%rdx
    c8e4:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    c8eb:	48 89 fa             	mov    %rdi,%rdx
    c8ee:	83 e2 07             	and    $0x7,%edx
    c8f1:	83 c2 03             	add    $0x3,%edx
    c8f4:	40 38 f2             	cmp    %sil,%dl
    c8f7:	7c 09                	jl     c902 <io_thread+0x11a2>
    c8f9:	40 84 f6             	test   %sil,%sil
    c8fc:	0f 85 93 03 00 00    	jne    cc95 <io_thread+0x1535>
    c902:	8b 17                	mov    (%rdi),%edx
    c904:	e9 10 fb ff ff       	jmp    c419 <io_thread+0xcb9>
    c909:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
              for (int i = 0; i < req->iovec_count; i++) {
    c910:	49 8d 7e 04          	lea    0x4(%r14),%rdi
    c914:	48 89 f8             	mov    %rdi,%rax
    c917:	48 c1 e8 03          	shr    $0x3,%rax
    c91b:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    c922:	48 89 f8             	mov    %rdi,%rax
    c925:	83 e0 07             	and    $0x7,%eax
    c928:	83 c0 03             	add    $0x3,%eax
    c92b:	38 d0                	cmp    %dl,%al
    c92d:	7c 08                	jl     c937 <io_thread+0x11d7>
    c92f:	84 d2                	test   %dl,%dl
    c931:	0f 85 89 04 00 00    	jne    cdc0 <io_thread+0x1660>
    c937:	49 89 fc             	mov    %rdi,%r12
    c93a:	45 8b 46 04          	mov    0x4(%r14),%r8d
    c93e:	48 89 f8             	mov    %rdi,%rax
    c941:	49 8d 6e 10          	lea    0x10(%r14),%rbp
    c945:	41 83 e4 07          	and    $0x7,%r12d
    c949:	45 31 ed             	xor    %r13d,%r13d
    c94c:	48 c1 e8 03          	shr    $0x3,%rax
    c950:	41 83 c4 03          	add    $0x3,%r12d
    c954:	45 85 c0             	test   %r8d,%r8d
    c957:	7e 5d                	jle    c9b6 <io_thread+0x1256>
    c959:	48 89 bc 24 a0 00 00 00 	mov    %rdi,0xa0(%rsp)
    c961:	48 89 9c 24 88 00 00 00 	mov    %rbx,0x88(%rsp)
    c969:	48 89 eb             	mov    %rbp,%rbx
    c96c:	48 89 c5             	mov    %rax,%rbp
    c96f:	90                   	nop
                  free(req->iov[i].iov_base);
    c970:	48 89 d9             	mov    %rbx,%rcx
    c973:	48 c1 e9 03          	shr    $0x3,%rcx
    c977:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    c97e:	0f 85 16 03 00 00    	jne    cc9a <io_thread+0x153a>
    c984:	48 8b 3b             	mov    (%rbx),%rdi
              for (int i = 0; i < req->iovec_count; i++) {
    c987:	41 83 c5 01          	add    $0x1,%r13d
                  free(req->iov[i].iov_base);
    c98b:	e8 10 7e ff ff       	call   47a0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    c990:	0f b6 8d 00 80 ff 7f 	movzbl 0x7fff8000(%rbp),%ecx
    c997:	41 38 cc             	cmp    %cl,%r12b
    c99a:	7c 08                	jl     c9a4 <io_thread+0x1244>
    c99c:	84 c9                	test   %cl,%cl
    c99e:	0f 85 fe 02 00 00    	jne    cca2 <io_thread+0x1542>
    c9a4:	48 83 c3 10          	add    $0x10,%rbx
    c9a8:	45 39 6e 04          	cmp    %r13d,0x4(%r14)
    c9ac:	7f c2                	jg     c970 <io_thread+0x1210>
    c9ae:	48 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%rbx
              close(req->client_socket);
    c9b6:	49 8d 7e 08          	lea    0x8(%r14),%rdi
    c9ba:	48 89 f8             	mov    %rdi,%rax
    c9bd:	48 c1 e8 03          	shr    $0x3,%rax
    c9c1:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    c9c8:	84 c0                	test   %al,%al
    c9ca:	74 08                	je     c9d4 <io_thread+0x1274>
    c9cc:	3c 03                	cmp    $0x3,%al
    c9ce:	0f 8e 5f 04 00 00    	jle    ce33 <io_thread+0x16d3>
    c9d4:	41 8b 7e 08          	mov    0x8(%r14),%edi
    c9d8:	e8 b3 7a ff ff       	call   4490 <close@plt>
              free(req);
    c9dd:	4c 89 f7             	mov    %r14,%rdi
    c9e0:	e8 bb 7d ff ff       	call   47a0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    c9e5:	4c 89 f8             	mov    %r15,%rax
    c9e8:	48 c1 e8 03          	shr    $0x3,%rax
    c9ec:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c9f3:	0f 84 6b f9 ff ff    	je     c364 <io_thread+0xc04>
    c9f9:	4c 89 ff             	mov    %r15,%rdi
    c9fc:	e8 df 7a ff ff       	call   44e0 <__asan_report_load8@plt>
    ca01:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
              if (!cqe->res) {
    ca08:	85 c0                	test   %eax,%eax
    ca0a:	75 54                	jne    ca60 <io_thread+0x1300>
                  fprintf(stderr, "Empty request!\n");
    ca0c:	48 8d 3d 8d 91 00 00 	lea    0x918d(%rip),%rdi        # 15ba0 <stderr@GLIBC_2.2.5>
    ca13:	48 89 f8             	mov    %rdi,%rax
    ca16:	48 c1 e8 03          	shr    $0x3,%rax
    ca1a:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ca21:	0f 85 49 06 00 00    	jne    d070 <io_thread+0x1910>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    ca27:	48 8b 0d 72 91 00 00 	mov    0x9172(%rip),%rcx        # 15ba0 <stderr@GLIBC_2.2.5>
    ca2e:	ba 0f 00 00 00       	mov    $0xf,%edx
    ca33:	be 01 00 00 00       	mov    $0x1,%esi
    ca38:	48 8d 3d 01 43 00 00 	lea    0x4301(%rip),%rdi        # 10d40 <_IO_stdin_used+0xd40>
    ca3f:	e8 5c 7a ff ff       	call   44a0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    ca44:	4c 89 f8             	mov    %r15,%rax
    ca47:	48 c1 e8 03          	shr    $0x3,%rax
    ca4b:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ca52:	0f 84 0c f9 ff ff    	je     c364 <io_thread+0xc04>
    ca58:	4c 89 ff             	mov    %r15,%rdi
    ca5b:	e8 80 7a ff ff       	call   44e0 <__asan_report_load8@plt>
    char http_request[1024];
    ca60:	4c 8d ab 60 fb ff ff 	lea    -0x4a0(%rbx),%r13
    ca67:	be 00 04 00 00       	mov    $0x400,%esi
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
    ca6c:	4d 8d 66 10          	lea    0x10(%r14),%r12
    char http_request[1024];
    ca70:	4c 89 ef             	mov    %r13,%rdi
    ca73:	e8 f8 7a ff ff       	call   4570 <__asan_unpoison_stack_memory@plt>
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
    ca78:	4c 89 e0             	mov    %r12,%rax
    ca7b:	48 c1 e8 03          	shr    $0x3,%rax
    ca7f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ca86:	0f 85 6d 05 00 00    	jne    cff9 <io_thread+0x1899>
    for (int i = 0; i < dest_sz; i++) {
    ca8c:	49 8b 46 10          	mov    0x10(%r14),%rax
    ca90:	4c 89 ef             	mov    %r13,%rdi
    ca93:	4c 8d 83 60 ff ff ff 	lea    -0xa0(%rbx),%r8
    ca9a:	eb 14                	jmp    cab0 <io_thread+0x1350>
    ca9c:	0f 1f 40 00          	nopl   0x0(%rax)
    caa0:	48 83 c7 01          	add    $0x1,%rdi
    caa4:	48 89 f0             	mov    %rsi,%rax
    caa7:	49 39 f8             	cmp    %rdi,%r8
    caaa:	0f 84 00 01 00 00    	je     cbb0 <io_thread+0x1450>
        dest[i] = src[i];
    cab0:	48 89 c2             	mov    %rax,%rdx
    cab3:	48 89 c1             	mov    %rax,%rcx
    cab6:	48 c1 ea 03          	shr    $0x3,%rdx
    caba:	83 e1 07             	and    $0x7,%ecx
    cabd:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    cac4:	38 ca                	cmp    %cl,%dl
    cac6:	7f 08                	jg     cad0 <io_thread+0x1370>
    cac8:	84 d2                	test   %dl,%dl
    caca:	0f 85 df 01 00 00    	jne    ccaf <io_thread+0x154f>
    cad0:	48 89 f9             	mov    %rdi,%rcx
    cad3:	48 89 fe             	mov    %rdi,%rsi
    cad6:	0f b6 10             	movzbl (%rax),%edx
    cad9:	48 c1 e9 03          	shr    $0x3,%rcx
    cadd:	83 e6 07             	and    $0x7,%esi
    cae0:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    cae7:	40 38 f1             	cmp    %sil,%cl
    caea:	7f 08                	jg     caf4 <io_thread+0x1394>
    caec:	84 c9                	test   %cl,%cl
    caee:	0f 85 c3 01 00 00    	jne    ccb7 <io_thread+0x1557>
    caf4:	88 17                	mov    %dl,(%rdi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    caf6:	48 8d 70 01          	lea    0x1(%rax),%rsi
    cafa:	80 fa 0d             	cmp    $0xd,%dl
    cafd:	75 a1                	jne    caa0 <io_thread+0x1340>
    caff:	48 89 f2             	mov    %rsi,%rdx
    cb02:	48 89 f1             	mov    %rsi,%rcx
    cb05:	48 c1 ea 03          	shr    $0x3,%rdx
    cb09:	83 e1 07             	and    $0x7,%ecx
    cb0c:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    cb13:	38 ca                	cmp    %cl,%dl
    cb15:	7f 08                	jg     cb1f <io_thread+0x13bf>
    cb17:	84 d2                	test   %dl,%dl
    cb19:	0f 85 99 02 00 00    	jne    cdb8 <io_thread+0x1658>
    cb1f:	80 78 01 0a          	cmpb   $0xa,0x1(%rax)
    cb23:	0f 85 77 ff ff ff    	jne    caa0 <io_thread+0x1340>
            dest[i] = '\0';
    cb29:	c6 07 00             	movb   $0x0,(%rdi)
    handle_http_method(http_request, req->client_socket, ring);
    cb2c:	49 8d 7e 08          	lea    0x8(%r14),%rdi
    cb30:	48 89 f8             	mov    %rdi,%rax
    cb33:	48 c1 e8 03          	shr    $0x3,%rax
    cb37:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    cb3e:	84 c0                	test   %al,%al
    cb40:	74 08                	je     cb4a <io_thread+0x13ea>
    cb42:	3c 03                	cmp    $0x3,%al
    cb44:	0f 8e a0 03 00 00    	jle    ceea <io_thread+0x178a>
    cb4a:	41 8b 76 08          	mov    0x8(%r14),%esi
    cb4e:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    cb53:	4c 89 ef             	mov    %r13,%rdi
    cb56:	e8 35 e2 ff ff       	call   ad90 <handle_http_method>
    return 0;
    cb5b:	be 00 04 00 00       	mov    $0x400,%esi
    cb60:	4c 89 ef             	mov    %r13,%rdi
    cb63:	e8 e8 78 ff ff       	call   4450 <__asan_poison_stack_memory@plt>
              free(req->iov[0].iov_base);
    cb68:	4c 89 e0             	mov    %r12,%rax
    cb6b:	48 c1 e8 03          	shr    $0x3,%rax
    cb6f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    cb76:	0f 85 66 03 00 00    	jne    cee2 <io_thread+0x1782>
    cb7c:	49 8b 7e 10          	mov    0x10(%r14),%rdi
    cb80:	e8 1b 7c ff ff       	call   47a0 <free@plt>
              free(req);
    cb85:	4c 89 f7             	mov    %r14,%rdi
    cb88:	e8 13 7c ff ff       	call   47a0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    cb8d:	4c 89 f8             	mov    %r15,%rax
    cb90:	48 c1 e8 03          	shr    $0x3,%rax
    cb94:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    cb9b:	0f 84 c3 f7 ff ff    	je     c364 <io_thread+0xc04>
    cba1:	4c 89 ff             	mov    %r15,%rdi
    cba4:	e8 37 79 ff ff       	call   44e0 <__asan_report_load8@plt>
    cba9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        fprintf(stderr, "Malformed request\n");
    cbb0:	48 8d 3d e9 8f 00 00 	lea    0x8fe9(%rip),%rdi        # 15ba0 <stderr@GLIBC_2.2.5>
    cbb7:	48 89 f8             	mov    %rdi,%rax
    cbba:	48 c1 e8 03          	shr    $0x3,%rax
    cbbe:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    cbc5:	0f 85 12 03 00 00    	jne    cedd <io_thread+0x177d>
    cbcb:	48 8b 0d ce 8f 00 00 	mov    0x8fce(%rip),%rcx        # 15ba0 <stderr@GLIBC_2.2.5>
    cbd2:	ba 12 00 00 00       	mov    $0x12,%edx
    cbd7:	be 01 00 00 00       	mov    $0x1,%esi
    cbdc:	48 8d 3d 7d 3e 00 00 	lea    0x3e7d(%rip),%rdi        # 10a60 <_IO_stdin_used+0xa60>
    cbe3:	e8 b8 78 ff ff       	call   44a0 <fwrite@plt>
        exit(1);
    cbe8:	e8 23 7a ff ff       	call   4610 <__asan_handle_no_return@plt>
    cbed:	bf 01 00 00 00       	mov    $0x1,%edi
    cbf2:	e8 19 79 ff ff       	call   4510 <exit@plt>
    cbf7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    cc00:	4c 8d bb e0 f9 ff ff 	lea    -0x620(%rbx),%r15
    cc07:	4c 89 f8             	mov    %r15,%rax
    cc0a:	48 c1 e8 03          	shr    $0x3,%rax
    cc0e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    cc15:	0f 85 75 02 00 00    	jne    ce90 <io_thread+0x1730>
    cc1b:	48 89 bb e0 f9 ff ff 	mov    %rdi,-0x620(%rbx)
	return err;
    cc22:	e9 04 fc ff ff       	jmp    c82b <io_thread+0x10cb>
    cc27:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    cc30:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    cc35:	48 8b ac 24 a8 00 00 00 	mov    0xa8(%rsp),%rbp
    cc3d:	48 c1 e8 03          	shr    $0x3,%rax
    cc41:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    cc48:	0f 85 b3 03 00 00    	jne    d001 <io_thread+0x18a1>
    cc4e:	48 8b bb a8 fa ff ff 	mov    -0x558(%rbx),%rdi
    cc55:	48 89 f8             	mov    %rdi,%rax
    cc58:	48 c1 e8 03          	shr    $0x3,%rax
    cc5c:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    cc63:	48 89 f8             	mov    %rdi,%rax
    cc66:	83 e0 07             	and    $0x7,%eax
    cc69:	83 c0 03             	add    $0x3,%eax
    cc6c:	38 d0                	cmp    %dl,%al
    cc6e:	7c 08                	jl     cc78 <io_thread+0x1518>
    cc70:	84 d2                	test   %dl,%dl
    cc72:	0f 85 20 02 00 00    	jne    ce98 <io_thread+0x1738>
    cc78:	8b 07                	mov    (%rdi),%eax
    cc7a:	83 c0 01             	add    $0x1,%eax
    cc7d:	89 07                	mov    %eax,(%rdi)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    cc7f:	48 8d 3d 9a 3f 00 00 	lea    0x3f9a(%rip),%rdi        # 10c20 <_IO_stdin_used+0xc20>
    cc86:	e8 75 7b ff ff       	call   4800 <puts@plt>
    cc8b:	e9 a0 fa ff ff       	jmp    c730 <io_thread+0xfd0>
		head = IO_URING_READ_ONCE(*sq->khead);
    cc90:	e8 bb 78 ff ff       	call   4550 <__asan_report_load4@plt>
		head = io_uring_smp_load_acquire(sq->khead);
    cc95:	e8 b6 78 ff ff       	call   4550 <__asan_report_load4@plt>
                  free(req->iov[i].iov_base);
    cc9a:	48 89 df             	mov    %rbx,%rdi
    cc9d:	e8 3e 78 ff ff       	call   44e0 <__asan_report_load8@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    cca2:	48 8b bc 24 a0 00 00 00 	mov    0xa0(%rsp),%rdi
    ccaa:	e8 a1 78 ff ff       	call   4550 <__asan_report_load4@plt>
        dest[i] = src[i];
    ccaf:	48 89 c7             	mov    %rax,%rdi
    ccb2:	e8 d9 7a ff ff       	call   4790 <__asan_report_load1@plt>
    ccb7:	e8 14 7b ff ff       	call   47d0 <__asan_report_store1@plt>
				cqe->user_data == LIBURING_UDATA_TIMEOUT) {
    ccbc:	e8 1f 78 ff ff       	call   44e0 <__asan_report_load8@plt>
			if (cqe->res < 0)
    ccc1:	4c 89 c7             	mov    %r8,%rdi
    ccc4:	e8 87 78 ff ff       	call   4550 <__asan_report_load4@plt>
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    ccc9:	4c 89 f7             	mov    %r14,%rdi
    cccc:	e8 0f 78 ff ff       	call   44e0 <__asan_report_load8@plt>
    ccd1:	e8 7a 78 ff ff       	call   4550 <__asan_report_load4@plt>
		unsigned head = *ring->cq.khead;
    ccd6:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
    ccdb:	e8 00 78 ff ff       	call   44e0 <__asan_report_load8@plt>
    cce0:	48 89 d7             	mov    %rdx,%rdi
    cce3:	e8 68 78 ff ff       	call   4550 <__asan_report_load4@plt>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    cce8:	4c 89 ef             	mov    %r13,%rdi
    cceb:	e8 f0 77 ff ff       	call   44e0 <__asan_report_load8@plt>
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    ccf0:	48 89 f7             	mov    %rsi,%rdi
    ccf3:	e8 58 78 ff ff       	call   4550 <__asan_report_load4@plt>
	if (next - head <= sq->ring_entries) {
    ccf8:	4c 89 df             	mov    %r11,%rdi
    ccfb:	e8 50 78 ff ff       	call   4550 <__asan_report_load4@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    cd00:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    cd05:	e8 46 78 ff ff       	call   4550 <__asan_report_load4@plt>
	*cqe_ptr = cqe;
    cd0a:	4c 89 ff             	mov    %r15,%rdi
    cd0d:	e8 be 79 ff ff       	call   46d0 <__asan_report_store8@plt>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    cd12:	4c 89 f7             	mov    %r14,%rdi
    cd15:	e8 36 78 ff ff       	call   4550 <__asan_report_load4@plt>
    cd1a:	f7 d8                	neg    %eax
    cd1c:	89 c7                	mov    %eax,%edi
    cd1e:	e8 bd 7a ff ff       	call   47e0 <strerror@plt>
    cd23:	48 8d 3d 76 8e 00 00 	lea    0x8e76(%rip),%rdi        # 15ba0 <stderr@GLIBC_2.2.5>
    cd2a:	48 89 c1             	mov    %rax,%rcx
    cd2d:	48 89 f8             	mov    %rdi,%rax
    cd30:	48 c1 e8 03          	shr    $0x3,%rax
    cd34:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    cd3b:	0f 85 5c 01 00 00    	jne    ce9d <io_thread+0x173d>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    cd41:	48 8b 3d 58 8e 00 00 	mov    0x8e58(%rip),%rdi        # 15ba0 <stderr@GLIBC_2.2.5>
    cd48:	45 89 e0             	mov    %r12d,%r8d
    cd4b:	be 01 00 00 00       	mov    $0x1,%esi
    cd50:	31 c0                	xor    %eax,%eax
    cd52:	48 8d 15 87 3f 00 00 	lea    0x3f87(%rip),%rdx        # 10ce0 <_IO_stdin_used+0xce0>
    cd59:	e8 f2 79 ff ff       	call   4750 <__fprintf_chk@plt>
          exit(1);
    cd5e:	e8 ad 78 ff ff       	call   4610 <__asan_handle_no_return@plt>
    cd63:	bf 01 00 00 00       	mov    $0x1,%edi
    cd68:	e8 a3 77 ff ff       	call   4510 <exit@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    cd6d:	48 89 f7             	mov    %rsi,%rdi
    cd70:	e8 db 77 ff ff       	call   4550 <__asan_report_load4@plt>
	if (ring->flags & IORING_SETUP_SQE128)
    cd75:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    cd7a:	e8 d1 77 ff ff       	call   4550 <__asan_report_load4@plt>
		head = IO_URING_READ_ONCE(*sq->khead);
    cd7f:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    cd84:	e8 57 77 ff ff       	call   44e0 <__asan_report_load8@plt>
	unsigned mask = ring->cq.ring_mask;
    cd89:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    cd8e:	e8 bd 77 ff ff       	call   4550 <__asan_report_load4@plt>
      if (cqe->res < 0) {
    cd93:	48 89 d7             	mov    %rdx,%rdi
    cd96:	e8 b5 77 ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->user_data = (unsigned long) data;
    cd9b:	48 89 c7             	mov    %rax,%rdi
    cd9e:	e8 2d 79 ff ff       	call   46d0 <__asan_report_store8@plt>
  while (data->running == 1) {
    cda3:	48 89 f7             	mov    %rsi,%rdi
    cda6:	e8 a5 77 ff ff       	call   4550 <__asan_report_load4@plt>
              add_read_request(cqe->res, &ring);
    cdab:	4c 89 ff             	mov    %r15,%rdi
    cdae:	e8 2d 77 ff ff       	call   44e0 <__asan_report_load8@plt>
    cdb3:	e8 98 77 ff ff       	call   4550 <__asan_report_load4@plt>
        if (src[i] == '\r' && src[i+1] == '\n') {
    cdb8:	48 89 f7             	mov    %rsi,%rdi
    cdbb:	e8 d0 79 ff ff       	call   4790 <__asan_report_load1@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    cdc0:	e8 8b 77 ff ff       	call   4550 <__asan_report_load4@plt>
      io_uring_cqe_seen(&ring, cqe);
    cdc5:	4c 89 ff             	mov    %r15,%rdi
    cdc8:	e8 13 77 ff ff       	call   44e0 <__asan_report_load8@plt>
      if (cqe->user_data == 1) {
    cdcd:	e8 0e 77 ff ff       	call   44e0 <__asan_report_load8@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    cdd2:	4c 89 ff             	mov    %r15,%rdi
    cdd5:	e8 06 77 ff ff       	call   44e0 <__asan_report_load8@plt>
    cdda:	e8 01 77 ff ff       	call   44e0 <__asan_report_load8@plt>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    cddf:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
    cde4:	e8 f7 76 ff ff       	call   44e0 <__asan_report_load8@plt>
    cde9:	e8 62 77 ff ff       	call   4550 <__asan_report_load4@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    cdee:	48 8b 7c 24 78       	mov    0x78(%rsp),%rdi
    cdf3:	e8 58 77 ff ff       	call   4550 <__asan_report_load4@plt>
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    cdf8:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    cdfd:	e8 4e 77 ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->opcode = (__u8) op;
    ce02:	e8 c9 79 ff ff       	call   47d0 <__asan_report_store1@plt>
	sqe->flags = 0;
    ce07:	48 89 c7             	mov    %rax,%rdi
    ce0a:	e8 c1 79 ff ff       	call   47d0 <__asan_report_store1@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    ce0f:	48 8b 7c 24 70       	mov    0x70(%rsp),%rdi
    ce14:	e8 c7 76 ff ff       	call   44e0 <__asan_report_load8@plt>
      if (cqe->user_data == 1) {
    ce19:	4c 89 ff             	mov    %r15,%rdi
    ce1c:	e8 bf 76 ff ff       	call   44e0 <__asan_report_load8@plt>
    ce21:	e8 ba 76 ff ff       	call   44e0 <__asan_report_load8@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    ce26:	4c 89 ff             	mov    %r15,%rdi
    ce29:	e8 b2 76 ff ff       	call   44e0 <__asan_report_load8@plt>
    ce2e:	e8 ad 76 ff ff       	call   44e0 <__asan_report_load8@plt>
              close(req->client_socket);
    ce33:	e8 18 77 ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->ioprio = 0;
    ce38:	48 89 d7             	mov    %rdx,%rdi
    ce3b:	e8 c0 76 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->fd = fd;
    ce40:	48 89 d7             	mov    %rdx,%rdi
    ce43:	e8 78 78 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->off = offset;
    ce48:	48 89 c7             	mov    %rax,%rdi
    ce4b:	e8 80 78 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->addr = (unsigned long) addr;
    ce50:	48 89 c7             	mov    %rax,%rdi
    ce53:	e8 78 78 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->len = len;
    ce58:	48 89 d7             	mov    %rdx,%rdi
    ce5b:	e8 60 78 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->rw_flags = 0;
    ce60:	48 89 d7             	mov    %rdx,%rdi
    ce63:	e8 58 78 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->buf_index = 0;
    ce68:	48 89 d7             	mov    %rdx,%rdi
    ce6b:	e8 90 76 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->personality = 0;
    ce70:	48 89 d7             	mov    %rdx,%rdi
    ce73:	e8 88 76 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->file_index = 0;
    ce78:	48 89 d7             	mov    %rdx,%rdi
    ce7b:	e8 40 78 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->addr3 = 0;
    ce80:	48 89 c7             	mov    %rax,%rdi
    ce83:	e8 48 78 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->__pad2[0] = 0;
    ce88:	48 89 c7             	mov    %rax,%rdi
    ce8b:	e8 40 78 ff ff       	call   46d0 <__asan_report_store8@plt>
	*cqe_ptr = cqe;
    ce90:	4c 89 ff             	mov    %r15,%rdi
    ce93:	e8 38 78 ff ff       	call   46d0 <__asan_report_store8@plt>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    ce98:	e8 b3 76 ff ff       	call   4550 <__asan_report_load4@plt>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    ce9d:	e8 3e 76 ff ff       	call   44e0 <__asan_report_load8@plt>
void* io_thread(void *arg) {
    cea2:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    cea7:	be 40 06 00 00       	mov    $0x640,%esi
    ceac:	48 c7 00 0e 36 e0 45 	movq   $0x45e0360e,(%rax)
    ceb3:	48 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%rdx
    cebb:	48 89 c7             	mov    %rax,%rdi
    cebe:	e8 bd 77 ff ff       	call   4680 <__asan_stack_free_5@plt>
    cec3:	e9 d9 f8 ff ff       	jmp    c7a1 <io_thread+0x1041>
}
    cec8:	e8 e3 77 ff ff       	call   46b0 <__stack_chk_fail@plt>
	sqe->__pad2[0] = 0;
    cecd:	48 89 c7             	mov    %rax,%rdi
    ced0:	e8 fb 77 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->user_data = (unsigned long) data;
    ced5:	48 89 c7             	mov    %rax,%rdi
    ced8:	e8 f3 77 ff ff       	call   46d0 <__asan_report_store8@plt>
        fprintf(stderr, "Malformed request\n");
    cedd:	e8 fe 75 ff ff       	call   44e0 <__asan_report_load8@plt>
              free(req->iov[0].iov_base);
    cee2:	4c 89 e7             	mov    %r12,%rdi
    cee5:	e8 f6 75 ff ff       	call   44e0 <__asan_report_load8@plt>
    handle_http_method(http_request, req->client_socket, ring);
    ceea:	e8 61 76 ff ff       	call   4550 <__asan_report_load4@plt>
  io_uring_register_eventfd(data->ring, 0);
    ceef:	4c 89 e7             	mov    %r12,%rdi
    cef2:	e8 e9 75 ff ff       	call   44e0 <__asan_report_load8@plt>
  struct io_uring ring = *data->ring;
    cef7:	be d8 00 00 00       	mov    $0xd8,%esi
    cefc:	e8 5f 76 ff ff       	call   4560 <__asan_report_load_n@plt>
    cf01:	be d8 00 00 00       	mov    $0xd8,%esi
    cf06:	48 89 cf             	mov    %rcx,%rdi
    cf09:	e8 72 76 ff ff       	call   4580 <__asan_report_store_n@plt>
    cf0e:	4c 89 e7             	mov    %r12,%rdi
    cf11:	e8 ca 75 ff ff       	call   44e0 <__asan_report_load8@plt>
void* io_thread(void *arg) {
    cf16:	bf 40 06 00 00       	mov    $0x640,%edi
    cf1b:	e8 50 78 ff ff       	call   4770 <__asan_stack_malloc_5@plt>
    cf20:	48 85 c0             	test   %rax,%rax
    cf23:	48 0f 44 44 24 58    	cmove  0x58(%rsp),%rax
    cf29:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    cf2e:	e9 6c e8 ff ff       	jmp    b79f <io_thread+0x3f>
		head = io_uring_smp_load_acquire(sq->khead);
    cf33:	e8 18 76 ff ff       	call   4550 <__asan_report_load4@plt>
		head = IO_URING_READ_ONCE(*sq->khead);
    cf38:	e8 13 76 ff ff       	call   4550 <__asan_report_load4@plt>
	if (next - head <= sq->ring_entries) {
    cf3d:	4c 89 d7             	mov    %r10,%rdi
    cf40:	e8 0b 76 ff ff       	call   4550 <__asan_report_load4@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    cf45:	48 89 f7             	mov    %rsi,%rdi
    cf48:	e8 93 75 ff ff       	call   44e0 <__asan_report_load8@plt>
    cf4d:	48 8b 7c 24 78       	mov    0x78(%rsp),%rdi
    cf52:	e8 f9 75 ff ff       	call   4550 <__asan_report_load4@plt>
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    cf57:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    cf5c:	e8 ef 75 ff ff       	call   4550 <__asan_report_load4@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    cf61:	48 89 f7             	mov    %rsi,%rdi
    cf64:	e8 e7 75 ff ff       	call   4550 <__asan_report_load4@plt>
  iov->iov_len = 10;
    cf69:	e8 62 77 ff ff       	call   46d0 <__asan_report_store8@plt>
  iov->iov_base = zh_malloc(10);
    cf6e:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    cf73:	e8 58 77 ff ff       	call   46d0 <__asan_report_store8@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    cf78:	48 8d 3d 21 8c 00 00 	lea    0x8c21(%rip),%rdi        # 15ba0 <stderr@GLIBC_2.2.5>
    cf7f:	48 89 f8             	mov    %rdi,%rax
    cf82:	48 c1 e8 03          	shr    $0x3,%rax
    cf86:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    cf8d:	75 65                	jne    cff4 <io_thread+0x1894>
    cf8f:	48 8b 0d 0a 8c 00 00 	mov    0x8c0a(%rip),%rcx        # 15ba0 <stderr@GLIBC_2.2.5>
    cf96:	ba 28 00 00 00       	mov    $0x28,%edx
    cf9b:	be 01 00 00 00       	mov    $0x1,%esi
    cfa0:	48 8d 3d b9 32 00 00 	lea    0x32b9(%rip),%rdi        # 10260 <_IO_stdin_used+0x260>
    cfa7:	e8 f4 74 ff ff       	call   44a0 <fwrite@plt>
        exit(1);
    cfac:	e8 5f 76 ff ff       	call   4610 <__asan_handle_no_return@plt>
    cfb1:	bf 01 00 00 00       	mov    $0x1,%edi
    cfb6:	e8 55 75 ff ff       	call   4510 <exit@plt>
  socklen_t client_addr_len = sizeof(client_addr);
    cfbb:	48 8b bc 24 80 00 00 00 	mov    0x80(%rsp),%rdi
    cfc3:	e8 f8 76 ff ff       	call   46c0 <__asan_report_store4@plt>
  int enable = 1;
    cfc8:	e8 f3 76 ff ff       	call   46c0 <__asan_report_store4@plt>
		head = IO_URING_READ_ONCE(*sq->khead);
    cfcd:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    cfd2:	e8 09 75 ff ff       	call   44e0 <__asan_report_load8@plt>
	if (ring->flags & IORING_SETUP_SQE128)
    cfd7:	48 89 f7             	mov    %rsi,%rdi
    cfda:	e8 71 75 ff ff       	call   4550 <__asan_report_load4@plt>
	*cqe_ptr = cqe;
    cfdf:	4c 89 ff             	mov    %r15,%rdi
    cfe2:	e8 e9 76 ff ff       	call   46d0 <__asan_report_store8@plt>
  srv_addr.sin_port = htons(port);
    cfe7:	e8 14 75 ff ff       	call   4500 <__asan_report_store2@plt>
  srv_addr.sin_family = AF_INET;
    cfec:	4c 89 e7             	mov    %r12,%rdi
    cfef:	e8 0c 75 ff ff       	call   4500 <__asan_report_store2@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    cff4:	e8 e7 74 ff ff       	call   44e0 <__asan_report_load8@plt>
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
    cff9:	4c 89 e7             	mov    %r12,%rdi
    cffc:	e8 df 74 ff ff       	call   44e0 <__asan_report_load8@plt>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    d001:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
    d006:	e8 d5 74 ff ff       	call   44e0 <__asan_report_load8@plt>
  while (data->running == 1) {
    d00b:	48 89 f7             	mov    %rsi,%rdi
    d00e:	e8 3d 75 ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->opcode = (__u8) op;
    d013:	e8 b8 77 ff ff       	call   47d0 <__asan_report_store1@plt>
	sqe->flags = 0;
    d018:	48 89 c7             	mov    %rax,%rdi
    d01b:	e8 b0 77 ff ff       	call   47d0 <__asan_report_store1@plt>
	sqe->ioprio = 0;
    d020:	48 89 d7             	mov    %rdx,%rdi
    d023:	e8 d8 74 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->fd = fd;
    d028:	48 89 d7             	mov    %rdx,%rdi
    d02b:	e8 90 76 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->off = offset;
    d030:	48 89 c7             	mov    %rax,%rdi
    d033:	e8 98 76 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->addr = (unsigned long) addr;
    d038:	48 89 c7             	mov    %rax,%rdi
    d03b:	e8 90 76 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->len = len;
    d040:	48 89 d7             	mov    %rdx,%rdi
    d043:	e8 78 76 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->rw_flags = 0;
    d048:	48 89 d7             	mov    %rdx,%rdi
    d04b:	e8 70 76 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->buf_index = 0;
    d050:	48 89 d7             	mov    %rdx,%rdi
    d053:	e8 a8 74 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->personality = 0;
    d058:	48 89 d7             	mov    %rdx,%rdi
    d05b:	e8 a0 74 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->file_index = 0;
    d060:	48 89 d7             	mov    %rdx,%rdi
    d063:	e8 58 76 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->addr3 = 0;
    d068:	48 89 c7             	mov    %rax,%rdi
    d06b:	e8 60 76 ff ff       	call   46d0 <__asan_report_store8@plt>
                  fprintf(stderr, "Empty request!\n");
    d070:	e8 6b 74 ff ff       	call   44e0 <__asan_report_load8@plt>
    d075:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

000000000000d080 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    d080:	f3 0f 1e fa          	endbr64
    d084:	41 57                	push   %r15
    d086:	41 56                	push   %r14
    d088:	41 55                	push   %r13
    d08a:	41 54                	push   %r12
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    d08c:	4c 8d a7 28 01 00 00 	lea    0x128(%rdi),%r12
int barriered_work_ingest(struct BarrierTask *data) {
    d093:	55                   	push   %rbp
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    d094:	4c 89 e0             	mov    %r12,%rax
int barriered_work_ingest(struct BarrierTask *data) {
    d097:	53                   	push   %rbx
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    d098:	48 c1 e8 03          	shr    $0x3,%rax
int barriered_work_ingest(struct BarrierTask *data) {
    d09c:	48 83 ec 18          	sub    $0x18,%rsp
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    d0a0:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d0a7:	0f 85 c5 03 00 00    	jne    d472 <barriered_work_ingest+0x3f2>
    d0ad:	4c 8b 97 28 01 00 00 	mov    0x128(%rdi),%r10
    d0b4:	49 89 fe             	mov    %rdi,%r14
    d0b7:	49 8d ba bc 00 00 00 	lea    0xbc(%r10),%rdi
    d0be:	48 89 f8             	mov    %rdi,%rax
    d0c1:	48 c1 e8 03          	shr    $0x3,%rax
    d0c5:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    d0cc:	48 89 f8             	mov    %rdi,%rax
    d0cf:	83 e0 07             	and    $0x7,%eax
    d0d2:	83 c0 03             	add    $0x3,%eax
    d0d5:	38 d0                	cmp    %dl,%al
    d0d7:	7c 08                	jl     d0e1 <barriered_work_ingest+0x61>
    d0d9:	84 d2                	test   %dl,%dl
    d0db:	0f 85 87 03 00 00    	jne    d468 <barriered_work_ingest+0x3e8>
    d0e1:	41 8b 92 bc 00 00 00 	mov    0xbc(%r10),%edx
    d0e8:	85 d2                	test   %edx,%edx
    d0ea:	0f 8e 13 01 00 00    	jle    d203 <barriered_work_ingest+0x183>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    d0f0:	49 8d 7a 50          	lea    0x50(%r10),%rdi
    d0f4:	48 89 f8             	mov    %rdi,%rax
    d0f7:	48 c1 e8 03          	shr    $0x3,%rax
    d0fb:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d102:	0f 85 5b 03 00 00    	jne    d463 <barriered_work_ingest+0x3e3>
        data->ingest_count++;
    d108:	49 8d 86 68 01 00 00 	lea    0x168(%r14),%rax
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    d10f:	4d 8b 5a 50          	mov    0x50(%r10),%r11
    d113:	45 31 ed             	xor    %r13d,%r13d
        data->ingest_count++;
    d116:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    d11b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    d120:	4e 8d 3c ed 00 00 00 00 	lea    0x0(,%r13,8),%r15
    d128:	4b 8d 3c 3b          	lea    (%r11,%r15,1),%rdi
    d12c:	48 89 f8             	mov    %rdi,%rax
    d12f:	48 c1 e8 03          	shr    $0x3,%rax
    d133:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d13a:	0f 85 e4 02 00 00    	jne    d424 <barriered_work_ingest+0x3a4>
    d140:	48 8b 3f             	mov    (%rdi),%rdi
    d143:	48 89 f8             	mov    %rdi,%rax
    d146:	48 c1 e8 03          	shr    $0x3,%rax
    d14a:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    d151:	84 c0                	test   %al,%al
    d153:	74 08                	je     d15d <barriered_work_ingest+0xdd>
    d155:	3c 03                	cmp    $0x3,%al
    d157:	0f 8e c2 02 00 00    	jle    d41f <barriered_work_ingest+0x39f>
    d15d:	8b 37                	mov    (%rdi),%esi
    d15f:	31 db                	xor    %ebx,%ebx
    d161:	4c 8d 4f 08          	lea    0x8(%rdi),%r9
    d165:	85 f6                	test   %esi,%esi
    d167:	0f 8e 89 00 00 00    	jle    d1f6 <barriered_work_ingest+0x176>
    d16d:	0f 1f 00             	nopl   (%rax)
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    d170:	4c 89 c8             	mov    %r9,%rax
    d173:	48 c1 e8 03          	shr    $0x3,%rax
    d177:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d17e:	0f 85 7c 02 00 00    	jne    d400 <barriered_work_ingest+0x380>
    d184:	48 8b 47 08          	mov    0x8(%rdi),%rax
    d188:	48 89 dd             	mov    %rbx,%rbp
    d18b:	48 c1 e5 08          	shl    $0x8,%rbp
    d18f:	48 01 e8             	add    %rbp,%rax
    d192:	48 8d 88 80 00 00 00 	lea    0x80(%rax),%rcx
    d199:	48 89 ca             	mov    %rcx,%rdx
    d19c:	48 c1 ea 03          	shr    $0x3,%rdx
    d1a0:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    d1a7:	84 d2                	test   %dl,%dl
    d1a9:	74 09                	je     d1b4 <barriered_work_ingest+0x134>
    d1ab:	80 fa 03             	cmp    $0x3,%dl
    d1ae:	0f 8e 54 02 00 00    	jle    d408 <barriered_work_ingest+0x388>
    d1b4:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    d1bb:	74 5b                	je     d218 <barriered_work_ingest+0x198>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    d1bd:	48 83 c3 01          	add    $0x1,%rbx
    d1c1:	39 de                	cmp    %ebx,%esi
    d1c3:	7f ab                	jg     d170 <barriered_work_ingest+0xf0>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    d1c5:	49 8d ba bc 00 00 00 	lea    0xbc(%r10),%rdi
    d1cc:	48 89 f8             	mov    %rdi,%rax
    d1cf:	48 c1 e8 03          	shr    $0x3,%rax
    d1d3:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    d1da:	48 89 f8             	mov    %rdi,%rax
    d1dd:	83 e0 07             	and    $0x7,%eax
    d1e0:	83 c0 03             	add    $0x3,%eax
    d1e3:	38 d0                	cmp    %dl,%al
    d1e5:	7c 08                	jl     d1ef <barriered_work_ingest+0x16f>
    d1e7:	84 d2                	test   %dl,%dl
    d1e9:	0f 85 7e 02 00 00    	jne    d46d <barriered_work_ingest+0x3ed>
    d1ef:	41 8b 92 bc 00 00 00 	mov    0xbc(%r10),%edx
    d1f6:	49 83 c5 01          	add    $0x1,%r13
    d1fa:	44 39 ea             	cmp    %r13d,%edx
    d1fd:	0f 8f 1d ff ff ff    	jg     d120 <barriered_work_ingest+0xa0>
}
    d203:	48 83 c4 18          	add    $0x18,%rsp
    d207:	31 c0                	xor    %eax,%eax
    d209:	5b                   	pop    %rbx
    d20a:	5d                   	pop    %rbp
    d20b:	41 5c                	pop    %r12
    d20d:	41 5d                	pop    %r13
    d20f:	41 5e                	pop    %r14
    d211:	41 5f                	pop    %r15
    d213:	c3                   	ret
    d214:	0f 1f 40 00          	nopl   0x0(%rax)
        data->ingest_count++;
    d218:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    d21d:	48 c1 ea 03          	shr    $0x3,%rdx
    d221:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    d228:	0f 85 e7 01 00 00    	jne    d415 <barriered_work_ingest+0x395>
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    d22e:	48 8d b8 88 00 00 00 	lea    0x88(%rax),%rdi
        data->ingest_count++;
    d235:	49 83 86 68 01 00 00 01 	addq   $0x1,0x168(%r14)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    d23d:	48 89 fa             	mov    %rdi,%rdx
    d240:	48 c1 ea 03          	shr    $0x3,%rdx
    d244:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    d24b:	0f 85 bf 01 00 00    	jne    d410 <barriered_work_ingest+0x390>
    d251:	48 8d b8 94 00 00 00 	lea    0x94(%rax),%rdi
    d258:	48 8b b0 88 00 00 00 	mov    0x88(%rax),%rsi
    d25f:	48 89 fa             	mov    %rdi,%rdx
    d262:	48 c1 ea 03          	shr    $0x3,%rdx
    d266:	0f b6 8a 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%ecx
    d26d:	48 89 fa             	mov    %rdi,%rdx
    d270:	83 e2 07             	and    $0x7,%edx
    d273:	83 c2 03             	add    $0x3,%edx
    d276:	38 ca                	cmp    %cl,%dl
    d278:	7c 08                	jl     d282 <barriered_work_ingest+0x202>
    d27a:	84 c9                	test   %cl,%cl
    d27c:	0f 85 b9 01 00 00    	jne    d43b <barriered_work_ingest+0x3bb>
    d282:	48 63 80 94 00 00 00 	movslq 0x94(%rax),%rax
    d289:	bf 04 00 00 00       	mov    $0x4,%edi
    d28e:	48 c1 e0 05          	shl    $0x5,%rax
    d292:	48 8d 74 06 10       	lea    0x10(%rsi,%rax,1),%rsi
    d297:	e8 e4 71 ff ff       	call   4480 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    d29c:	4c 89 e0             	mov    %r12,%rax
    d29f:	48 c1 e8 03          	shr    $0x3,%rax
    d2a3:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d2aa:	0f 85 83 01 00 00    	jne    d433 <barriered_work_ingest+0x3b3>
    d2b0:	49 8b 86 28 01 00 00 	mov    0x128(%r14),%rax
    d2b7:	48 8d 78 50          	lea    0x50(%rax),%rdi
    d2bb:	48 89 fa             	mov    %rdi,%rdx
    d2be:	48 c1 ea 03          	shr    $0x3,%rdx
    d2c2:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    d2c9:	0f 85 5f 01 00 00    	jne    d42e <barriered_work_ingest+0x3ae>
    d2cf:	48 8b 78 50          	mov    0x50(%rax),%rdi
    d2d3:	4c 01 ff             	add    %r15,%rdi
    d2d6:	48 89 f8             	mov    %rdi,%rax
    d2d9:	48 c1 e8 03          	shr    $0x3,%rax
    d2dd:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d2e4:	0f 85 3f 01 00 00    	jne    d429 <barriered_work_ingest+0x3a9>
    d2ea:	48 8b 07             	mov    (%rdi),%rax
    d2ed:	48 8d 78 08          	lea    0x8(%rax),%rdi
    d2f1:	48 89 fa             	mov    %rdi,%rdx
    d2f4:	48 c1 ea 03          	shr    $0x3,%rdx
    d2f8:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    d2ff:	0f 85 59 01 00 00    	jne    d45e <barriered_work_ingest+0x3de>
    d305:	48 03 68 08          	add    0x8(%rax),%rbp
    d309:	48 8d bd 94 00 00 00 	lea    0x94(%rbp),%rdi
    d310:	48 89 f8             	mov    %rdi,%rax
    d313:	48 c1 e8 03          	shr    $0x3,%rax
    d317:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    d31e:	48 89 f8             	mov    %rdi,%rax
    d321:	83 e0 07             	and    $0x7,%eax
    d324:	83 c0 03             	add    $0x3,%eax
    d327:	38 d0                	cmp    %dl,%al
    d329:	7c 08                	jl     d333 <barriered_work_ingest+0x2b3>
    d32b:	84 d2                	test   %dl,%dl
    d32d:	0f 85 26 01 00 00    	jne    d459 <barriered_work_ingest+0x3d9>
    d333:	48 8d bd 90 00 00 00 	lea    0x90(%rbp),%rdi
    d33a:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    d340:	48 89 fa             	mov    %rdi,%rdx
    d343:	48 c1 ea 03          	shr    $0x3,%rdx
    d347:	83 c0 01             	add    $0x1,%eax
    d34a:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    d351:	84 d2                	test   %dl,%dl
    d353:	74 09                	je     d35e <barriered_work_ingest+0x2de>
    d355:	80 fa 03             	cmp    $0x3,%dl
    d358:	0f 8e f6 00 00 00    	jle    d454 <barriered_work_ingest+0x3d4>
    d35e:	99                   	cltd
        data->thread->buffers[b]->buffer[x].available = 0;
    d35f:	48 8d bd 80 00 00 00 	lea    0x80(%rbp),%rdi
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    d366:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
        data->thread->buffers[b]->buffer[x].available = 0;
    d36c:	48 89 f8             	mov    %rdi,%rax
    d36f:	48 c1 e8 03          	shr    $0x3,%rax
    d373:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    d37a:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        data->thread->buffers[b]->buffer[x].available = 0;
    d380:	84 c0                	test   %al,%al
    d382:	74 08                	je     d38c <barriered_work_ingest+0x30c>
    d384:	3c 03                	cmp    $0x3,%al
    d386:	0f 8e c3 00 00 00    	jle    d44f <barriered_work_ingest+0x3cf>
    d38c:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        asm volatile ("sfence" ::: "memory");
    d396:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    d399:	4d 8b 96 28 01 00 00 	mov    0x128(%r14),%r10
    d3a0:	49 8d 7a 50          	lea    0x50(%r10),%rdi
    d3a4:	48 89 f8             	mov    %rdi,%rax
    d3a7:	48 c1 e8 03          	shr    $0x3,%rax
    d3ab:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d3b2:	0f 85 92 00 00 00    	jne    d44a <barriered_work_ingest+0x3ca>
    d3b8:	4d 8b 5a 50          	mov    0x50(%r10),%r11
    d3bc:	4b 8d 3c 3b          	lea    (%r11,%r15,1),%rdi
    d3c0:	48 89 f8             	mov    %rdi,%rax
    d3c3:	48 c1 e8 03          	shr    $0x3,%rax
    d3c7:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d3ce:	75 75                	jne    d445 <barriered_work_ingest+0x3c5>
    d3d0:	48 8b 3f             	mov    (%rdi),%rdi
    d3d3:	48 89 f8             	mov    %rdi,%rax
    d3d6:	48 c1 e8 03          	shr    $0x3,%rax
    d3da:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    d3e1:	84 c0                	test   %al,%al
    d3e3:	74 04                	je     d3e9 <barriered_work_ingest+0x369>
    d3e5:	3c 03                	cmp    $0x3,%al
    d3e7:	7e 57                	jle    d440 <barriered_work_ingest+0x3c0>
    d3e9:	8b 37                	mov    (%rdi),%esi
    d3eb:	48 83 c3 01          	add    $0x1,%rbx
    d3ef:	39 de                	cmp    %ebx,%esi
    d3f1:	0f 8e ce fd ff ff    	jle    d1c5 <barriered_work_ingest+0x145>
    d3f7:	4c 8d 4f 08          	lea    0x8(%rdi),%r9
    d3fb:	e9 70 fd ff ff       	jmp    d170 <barriered_work_ingest+0xf0>
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    d400:	4c 89 cf             	mov    %r9,%rdi
    d403:	e8 d8 70 ff ff       	call   44e0 <__asan_report_load8@plt>
    d408:	48 89 cf             	mov    %rcx,%rdi
    d40b:	e8 40 71 ff ff       	call   4550 <__asan_report_load4@plt>
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    d410:	e8 cb 70 ff ff       	call   44e0 <__asan_report_load8@plt>
        data->ingest_count++;
    d415:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    d41a:	e8 c1 70 ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    d41f:	e8 2c 71 ff ff       	call   4550 <__asan_report_load4@plt>
    d424:	e8 b7 70 ff ff       	call   44e0 <__asan_report_load8@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    d429:	e8 b2 70 ff ff       	call   44e0 <__asan_report_load8@plt>
    d42e:	e8 ad 70 ff ff       	call   44e0 <__asan_report_load8@plt>
    d433:	4c 89 e7             	mov    %r12,%rdi
    d436:	e8 a5 70 ff ff       	call   44e0 <__asan_report_load8@plt>
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    d43b:	e8 10 71 ff ff       	call   4550 <__asan_report_load4@plt>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    d440:	e8 0b 71 ff ff       	call   4550 <__asan_report_load4@plt>
    d445:	e8 96 70 ff ff       	call   44e0 <__asan_report_load8@plt>
    d44a:	e8 91 70 ff ff       	call   44e0 <__asan_report_load8@plt>
        data->thread->buffers[b]->buffer[x].available = 0;
    d44f:	e8 6c 72 ff ff       	call   46c0 <__asan_report_store4@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    d454:	e8 f7 70 ff ff       	call   4550 <__asan_report_load4@plt>
    d459:	e8 f2 70 ff ff       	call   4550 <__asan_report_load4@plt>
    d45e:	e8 7d 70 ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    d463:	e8 78 70 ff ff       	call   44e0 <__asan_report_load8@plt>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    d468:	e8 e3 70 ff ff       	call   4550 <__asan_report_load4@plt>
    d46d:	e8 de 70 ff ff       	call   4550 <__asan_report_load4@plt>
    d472:	4c 89 e7             	mov    %r12,%rdi
    d475:	e8 66 70 ff ff       	call   44e0 <__asan_report_load8@plt>
    d47a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

000000000000d480 <barriered_thread>:
void* barriered_thread(void *arg) {
    d480:	f3 0f 1e fa          	endbr64
    d484:	41 57                	push   %r15
    d486:	48 8d 47 44          	lea    0x44(%rdi),%rax
    d48a:	41 56                	push   %r14
    d48c:	41 55                	push   %r13
  int t = 0;
    d48e:	45 31 ed             	xor    %r13d,%r13d
void* barriered_thread(void *arg) {
    d491:	41 54                	push   %r12
    d493:	55                   	push   %rbp
    d494:	53                   	push   %rbx
    d495:	48 89 fb             	mov    %rdi,%rbx
    d498:	48 83 ec 48          	sub    $0x48,%rsp
    d49c:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
  while (data->running == 1) {
    d4a1:	83 e0 07             	and    $0x7,%eax
    d4a4:	83 c0 03             	add    $0x3,%eax
  int waiting = 0;
    d4a7:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  while (data->running == 1) {
    d4af:	88 44 24 3f          	mov    %al,0x3f(%rsp)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    d4b3:	48 8d 47 04          	lea    0x4(%rdi),%rax
    d4b7:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    d4bc:	83 e0 07             	and    $0x7,%eax
    d4bf:	83 c0 03             	add    $0x3,%eax
    d4c2:	88 44 24 3e          	mov    %al,0x3e(%rsp)
  while (data->running == 1) {
    d4c6:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    d4cb:	48 c1 e8 03          	shr    $0x3,%rax
    d4cf:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    d4d6:	38 44 24 3f          	cmp    %al,0x3f(%rsp)
    d4da:	7c 08                	jl     d4e4 <barriered_thread+0x64>
    d4dc:	84 c0                	test   %al,%al
    d4de:	0f 85 3e 09 00 00    	jne    de22 <barriered_thread+0x9a2>
    d4e4:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    d4e8:	0f 85 5a 06 00 00    	jne    db48 <barriered_thread+0x6c8>
    if (t >= data->task_count) {
    d4ee:	4c 8d 7b 40          	lea    0x40(%rbx),%r15
    d4f2:	4c 89 f8             	mov    %r15,%rax
    d4f5:	48 c1 e8 03          	shr    $0x3,%rax
    d4f9:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    d500:	84 c0                	test   %al,%al
    d502:	74 08                	je     d50c <barriered_thread+0x8c>
    d504:	3c 03                	cmp    $0x3,%al
    d506:	0f 8e 0e 09 00 00    	jle    de1a <barriered_thread+0x99a>
    d50c:	8b 53 40             	mov    0x40(%rbx),%edx
    d50f:	90                   	nop
    d510:	41 39 d5             	cmp    %edx,%r13d
    d513:	0f 8d 57 07 00 00    	jge    dc70 <barriered_thread+0x7f0>
    d519:	48 8d 43 38          	lea    0x38(%rbx),%rax
    d51d:	4d 63 e5             	movslq %r13d,%r12
      if (data->tasks[t].available == 1) {
    d520:	48 89 c5             	mov    %rax,%rbp
    d523:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    d528:	49 c1 e4 09          	shl    $0x9,%r12
    d52c:	48 c1 ed 03          	shr    $0x3,%rbp
    d530:	e9 b1 00 00 00       	jmp    d5e6 <barriered_thread+0x166>
    d535:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    d538:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    d53c:	48 89 f8             	mov    %rdi,%rax
    d53f:	48 c1 e8 03          	shr    $0x3,%rax
    d543:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d54a:	0f 85 47 08 00 00    	jne    dd97 <barriered_thread+0x917>
    d550:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    d555:	48 8b 53 18          	mov    0x18(%rbx),%rdx
    d559:	48 c1 e8 03          	shr    $0x3,%rax
    d55d:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    d564:	38 44 24 3e          	cmp    %al,0x3e(%rsp)
    d568:	7c 08                	jl     d572 <barriered_thread+0xf2>
    d56a:	84 c0                	test   %al,%al
    d56c:	0f 85 2a 08 00 00    	jne    dd9c <barriered_thread+0x91c>
    d572:	48 63 43 04          	movslq 0x4(%rbx),%rax
    d576:	48 8d 3c c2          	lea    (%rdx,%rax,8),%rdi
    d57a:	48 89 f8             	mov    %rdi,%rax
    d57d:	48 c1 e8 03          	shr    $0x3,%rax
    d581:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d588:	0f 85 18 08 00 00    	jne    dda6 <barriered_thread+0x926>
    d58e:	48 8b 07             	mov    (%rdi),%rax
    d591:	48 8d 78 38          	lea    0x38(%rax),%rdi
    d595:	48 89 fa             	mov    %rdi,%rdx
    d598:	48 c1 ea 03          	shr    $0x3,%rdx
    d59c:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    d5a3:	0f 85 e9 07 00 00    	jne    dd92 <barriered_thread+0x912>
    d5a9:	48 8b 78 38          	mov    0x38(%rax),%rdi
    d5ad:	4c 01 e7             	add    %r12,%rdi
    d5b0:	e8 cb fa ff ff       	call   d080 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    d5b5:	4c 89 f8             	mov    %r15,%rax
    d5b8:	41 83 c5 01          	add    $0x1,%r13d
    d5bc:	48 c1 e8 03          	shr    $0x3,%rax
    d5c0:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    d5c7:	84 c0                	test   %al,%al
    d5c9:	74 08                	je     d5d3 <barriered_thread+0x153>
    d5cb:	3c 03                	cmp    $0x3,%al
    d5cd:	0f 8e a8 07 00 00    	jle    dd7b <barriered_thread+0x8fb>
    d5d3:	8b 53 40             	mov    0x40(%rbx),%edx
    d5d6:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    d5dd:	44 39 ea             	cmp    %r13d,%edx
    d5e0:	0f 8e 3a 05 00 00    	jle    db20 <barriered_thread+0x6a0>
      if (data->tasks[t].available == 1) {
    d5e6:	80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rbp)
    d5ed:	0f 85 90 07 00 00    	jne    dd83 <barriered_thread+0x903>
    d5f3:	48 8b 4b 38          	mov    0x38(%rbx),%rcx
    d5f7:	4c 01 e1             	add    %r12,%rcx
    d5fa:	48 8d b9 44 01 00 00 	lea    0x144(%rcx),%rdi
    d601:	48 89 f8             	mov    %rdi,%rax
    d604:	48 c1 e8 03          	shr    $0x3,%rax
    d608:	0f b6 b0 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%esi
    d60f:	48 89 f8             	mov    %rdi,%rax
    d612:	83 e0 07             	and    $0x7,%eax
    d615:	83 c0 03             	add    $0x3,%eax
    d618:	40 38 f0             	cmp    %sil,%al
    d61b:	7c 09                	jl     d626 <barriered_thread+0x1a6>
    d61d:	40 84 f6             	test   %sil,%sil
    d620:	0f 85 67 07 00 00    	jne    dd8d <barriered_thread+0x90d>
    d626:	83 b9 44 01 00 00 01 	cmpl   $0x1,0x144(%rcx)
    d62d:	0f 85 05 ff ff ff    	jne    d538 <barriered_thread+0xb8>
          previous = t - 1;
    d633:	41 8d 45 ff          	lea    -0x1(%r13),%eax
    d637:	83 ea 01             	sub    $0x1,%edx
    d63a:	45 85 ed             	test   %r13d,%r13d
    d63d:	0f 4f d0             	cmovg  %eax,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    d640:	48 8d 43 28          	lea    0x28(%rbx),%rax
    d644:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    d649:	48 c1 e8 03          	shr    $0x3,%rax
    d64d:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    d654:	84 c0                	test   %al,%al
    d656:	74 08                	je     d660 <barriered_thread+0x1e0>
    d658:	3c 03                	cmp    $0x3,%al
    d65a:	0f 8e 4b 07 00 00    	jle    ddab <barriered_thread+0x92b>
    d660:	8b 43 28             	mov    0x28(%rbx),%eax
    d663:	85 c0                	test   %eax,%eax
    d665:	0f 8e 45 05 00 00    	jle    dbb0 <barriered_thread+0x730>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    d66b:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    d66f:	48 89 fe             	mov    %rdi,%rsi
    d672:	48 c1 ee 03          	shr    $0x3,%rsi
    d676:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    d67d:	0f 85 b5 07 00 00    	jne    de38 <barriered_thread+0x9b8>
    d683:	4c 8d 81 80 00 00 00 	lea    0x80(%rcx),%r8
    d68a:	48 63 d2             	movslq %edx,%rdx
    d68d:	48 8b 7b 18          	mov    0x18(%rbx),%rdi
    d691:	4c 89 c6             	mov    %r8,%rsi
    d694:	48 c1 e2 09          	shl    $0x9,%rdx
    d698:	48 c1 ee 03          	shr    $0x3,%rsi
    d69c:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    d6a3:	40 84 f6             	test   %sil,%sil
    d6a6:	74 0a                	je     d6b2 <barriered_thread+0x232>
    d6a8:	40 80 fe 03          	cmp    $0x3,%sil
    d6ac:	0f 8e 7e 07 00 00    	jle    de30 <barriered_thread+0x9b0>
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    d6b2:	4c 8d 81 00 01 00 00 	lea    0x100(%rcx),%r8
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    d6b9:	44 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    d6c0:	4c 89 c6             	mov    %r8,%rsi
    d6c3:	48 c1 ee 03          	shr    $0x3,%rsi
    d6c7:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    d6ce:	40 84 f6             	test   %sil,%sil
    d6d1:	74 0a                	je     d6dd <barriered_thread+0x25d>
    d6d3:	40 80 fe 03          	cmp    $0x3,%sil
    d6d7:	0f 8e 9b 07 00 00    	jle    de78 <barriered_thread+0x9f8>
        int arrived = 0; 
    d6dd:	44 89 6c 24 18       	mov    %r13d,0x18(%rsp)
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    d6e2:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    d6e9:	48 63 c8             	movslq %eax,%rcx
        int prearrive = 0; 
    d6ec:	45 31 d2             	xor    %r10d,%r10d
    d6ef:	48 8d 34 cf          	lea    (%rdi,%rcx,8),%rsi
        int arrived = 0; 
    d6f3:	45 31 f6             	xor    %r14d,%r14d
    d6f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    d700:	48 89 f9             	mov    %rdi,%rcx
    d703:	48 c1 e9 03          	shr    $0x3,%rcx
    d707:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    d70e:	0f 85 62 06 00 00    	jne    dd76 <barriered_thread+0x8f6>
    d714:	4c 8b 1f             	mov    (%rdi),%r11
    d717:	49 8d 4b 38          	lea    0x38(%r11),%rcx
    d71b:	49 89 cd             	mov    %rcx,%r13
    d71e:	49 c1 ed 03          	shr    $0x3,%r13
    d722:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    d72a:	0f 85 3e 06 00 00    	jne    dd6e <barriered_thread+0x8ee>
    d730:	49 8b 4b 38          	mov    0x38(%r11),%rcx
    d734:	48 01 d1             	add    %rdx,%rcx
    d737:	4c 8d 99 80 00 00 00 	lea    0x80(%rcx),%r11
    d73e:	4d 89 dd             	mov    %r11,%r13
    d741:	49 c1 ed 03          	shr    $0x3,%r13
    d745:	45 0f b6 ad 00 80 ff 7f 	movzbl 0x7fff8000(%r13),%r13d
    d74d:	45 84 ed             	test   %r13b,%r13b
    d750:	74 0a                	je     d75c <barriered_thread+0x2dc>
    d752:	41 80 fd 03          	cmp    $0x3,%r13b
    d756:	0f 8e 0a 06 00 00    	jle    dd66 <barriered_thread+0x8e6>
    d75c:	44 39 89 80 00 00 00 	cmp    %r9d,0x80(%rcx)
    d763:	75 04                	jne    d769 <barriered_thread+0x2e9>
            arrived++;
    d765:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    d769:	4c 8d 99 00 01 00 00 	lea    0x100(%rcx),%r11
    d770:	4d 89 dd             	mov    %r11,%r13
    d773:	49 c1 ed 03          	shr    $0x3,%r13
    d777:	45 0f b6 ad 00 80 ff 7f 	movzbl 0x7fff8000(%r13),%r13d
    d77f:	45 84 ed             	test   %r13b,%r13b
    d782:	74 0a                	je     d78e <barriered_thread+0x30e>
    d784:	41 80 fd 03          	cmp    $0x3,%r13b
    d788:	0f 8e d0 05 00 00    	jle    dd5e <barriered_thread+0x8de>
    d78e:	44 39 81 00 01 00 00 	cmp    %r8d,0x100(%rcx)
    d795:	75 04                	jne    d79b <barriered_thread+0x31b>
            prearrive++;
    d797:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    d79b:	48 83 c7 08          	add    $0x8,%rdi
    d79f:	48 39 fe             	cmp    %rdi,%rsi
    d7a2:	0f 85 58 ff ff ff    	jne    d700 <barriered_thread+0x280>
        if (prearrive == 0 || prearrive == data->thread_count) {
    d7a8:	44 8b 6c 24 18       	mov    0x18(%rsp),%r13d
    d7ad:	45 85 d2             	test   %r10d,%r10d
    d7b0:	0f 84 32 02 00 00    	je     d9e8 <barriered_thread+0x568>
    d7b6:	41 39 c2             	cmp    %eax,%r10d
    d7b9:	0f 84 29 02 00 00    	je     d9e8 <barriered_thread+0x568>
        if (arrived == 0 || arrived == data->thread_count) {
    d7bf:	45 85 f6             	test   %r14d,%r14d
    d7c2:	74 26                	je     d7ea <barriered_thread+0x36a>
    d7c4:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    d7c9:	48 c1 e8 03          	shr    $0x3,%rax
    d7cd:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    d7d4:	84 c0                	test   %al,%al
    d7d6:	74 08                	je     d7e0 <barriered_thread+0x360>
    d7d8:	3c 03                	cmp    $0x3,%al
    d7da:	0f 8e 68 06 00 00    	jle    de48 <barriered_thread+0x9c8>
    d7e0:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    d7e4:	0f 85 b9 04 00 00    	jne    dca3 <barriered_thread+0x823>
          data->tasks[t].prearrive++;
    d7ea:	80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rbp)
    d7f1:	0f 85 d2 05 00 00    	jne    ddc9 <barriered_thread+0x949>
    d7f7:	48 8b 43 38          	mov    0x38(%rbx),%rax
    d7fb:	4c 01 e0             	add    %r12,%rax
    d7fe:	48 8d b8 00 01 00 00 	lea    0x100(%rax),%rdi
    d805:	48 89 fa             	mov    %rdi,%rdx
    d808:	48 c1 ea 03          	shr    $0x3,%rdx
    d80c:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    d813:	84 d2                	test   %dl,%dl
    d815:	74 09                	je     d820 <barriered_thread+0x3a0>
    d817:	80 fa 03             	cmp    $0x3,%dl
    d81a:	0f 8e de 05 00 00    	jle    ddfe <barriered_thread+0x97e>
    d820:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    d827:	45 85 ed             	test   %r13d,%r13d
    d82a:	75 4a                	jne    d876 <barriered_thread+0x3f6>
    d82c:	48 8d bb 80 00 00 00 	lea    0x80(%rbx),%rdi
    d833:	48 89 fa             	mov    %rdi,%rdx
    d836:	48 c1 ea 03          	shr    $0x3,%rdx
    d83a:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    d841:	0f 85 1a 06 00 00    	jne    de61 <barriered_thread+0x9e1>
    d847:	48 8d bb 88 00 00 00 	lea    0x88(%rbx),%rdi
    d84e:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    d855:	48 89 fa             	mov    %rdi,%rdx
    d858:	48 c1 ea 03          	shr    $0x3,%rdx
    d85c:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    d863:	0f 85 f3 05 00 00    	jne    de5c <barriered_thread+0x9dc>
    d869:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    d870:	0f 8c ea 02 00 00    	jl     db60 <barriered_thread+0x6e0>
          data->tasks[t].available = 0;
    d876:	48 8d b8 44 01 00 00 	lea    0x144(%rax),%rdi
    d87d:	48 89 fa             	mov    %rdi,%rdx
    d880:	48 c1 ea 03          	shr    $0x3,%rdx
    d884:	0f b6 8a 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%ecx
    d88b:	48 89 fa             	mov    %rdi,%rdx
    d88e:	83 e2 07             	and    $0x7,%edx
    d891:	83 c2 03             	add    $0x3,%edx
    d894:	38 ca                	cmp    %cl,%dl
    d896:	7c 08                	jl     d8a0 <barriered_thread+0x420>
    d898:	84 c9                	test   %cl,%cl
    d89a:	0f 85 38 05 00 00    	jne    ddd8 <barriered_thread+0x958>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    d8a0:	48 8d b8 18 01 00 00 	lea    0x118(%rax),%rdi
          data->tasks[t].available = 0;
    d8a7:	c7 80 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    d8b1:	48 89 fa             	mov    %rdi,%rdx
    d8b4:	48 c1 ea 03          	shr    $0x3,%rdx
    d8b8:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    d8bf:	0f 85 0e 05 00 00    	jne    ddd3 <barriered_thread+0x953>
    d8c5:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    d8c9:	48 8b 90 18 01 00 00 	mov    0x118(%rax),%rdx
    d8d0:	48 89 f8             	mov    %rdi,%rax
    d8d3:	48 c1 e8 03          	shr    $0x3,%rax
    d8d7:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d8de:	0f 85 e0 04 00 00    	jne    ddc4 <barriered_thread+0x944>
    d8e4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    d8e9:	48 8b 4b 18          	mov    0x18(%rbx),%rcx
    d8ed:	48 c1 e8 03          	shr    $0x3,%rax
    d8f1:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    d8f8:	38 44 24 3e          	cmp    %al,0x3e(%rsp)
    d8fc:	7c 08                	jl     d906 <barriered_thread+0x486>
    d8fe:	84 c0                	test   %al,%al
    d900:	0f 85 b4 04 00 00    	jne    ddba <barriered_thread+0x93a>
    d906:	48 63 43 04          	movslq 0x4(%rbx),%rax
    d90a:	48 8d 3c c1          	lea    (%rcx,%rax,8),%rdi
    d90e:	48 89 f8             	mov    %rdi,%rax
    d911:	48 c1 e8 03          	shr    $0x3,%rax
    d915:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d91c:	0f 85 93 04 00 00    	jne    ddb5 <barriered_thread+0x935>
    d922:	48 8b 07             	mov    (%rdi),%rax
    d925:	48 8d 78 38          	lea    0x38(%rax),%rdi
    d929:	48 89 f9             	mov    %rdi,%rcx
    d92c:	48 c1 e9 03          	shr    $0x3,%rcx
    d930:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    d937:	0f 85 bc 04 00 00    	jne    ddf9 <barriered_thread+0x979>
    d93d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    d941:	4c 01 e7             	add    %r12,%rdi
    d944:	ff d2                	call   *%rdx
          data->tasks[t].arrived++;
    d946:	80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rbp)
    d94d:	0f 85 9c 04 00 00    	jne    ddef <barriered_thread+0x96f>
    d953:	48 8b 43 38          	mov    0x38(%rbx),%rax
    d957:	4c 01 e0             	add    %r12,%rax
    d95a:	48 8d b8 80 00 00 00 	lea    0x80(%rax),%rdi
    d961:	48 89 fa             	mov    %rdi,%rdx
    d964:	48 c1 ea 03          	shr    $0x3,%rdx
    d968:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    d96f:	84 d2                	test   %dl,%dl
    d971:	74 09                	je     d97c <barriered_thread+0x4fc>
    d973:	80 fa 03             	cmp    $0x3,%dl
    d976:	0f 8e 6e 04 00 00    	jle    ddea <barriered_thread+0x96a>
          data->iteration_count++;
    d97c:	48 8d 7b 78          	lea    0x78(%rbx),%rdi
          data->tasks[t].arrived++;
    d980:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          data->iteration_count++;
    d987:	48 89 f8             	mov    %rdi,%rax
    d98a:	48 c1 e8 03          	shr    $0x3,%rax
    d98e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d995:	0f 85 4a 04 00 00    	jne    dde5 <barriered_thread+0x965>
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    d99b:	4c 89 f8             	mov    %r15,%rax
          data->iteration_count++;
    d99e:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    d9a3:	48 c1 e8 03          	shr    $0x3,%rax
    d9a7:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    d9ae:	84 c0                	test   %al,%al
    d9b0:	74 08                	je     d9ba <barriered_thread+0x53a>
    d9b2:	3c 03                	cmp    $0x3,%al
    d9b4:	0f 8e 23 04 00 00    	jle    dddd <barriered_thread+0x95d>
    d9ba:	8b 43 40             	mov    0x40(%rbx),%eax
    d9bd:	83 e8 01             	sub    $0x1,%eax
    d9c0:	44 39 e8             	cmp    %r13d,%eax
    d9c3:	74 3b                	je     da00 <barriered_thread+0x580>
          asm volatile ("sfence" ::: "memory");
    d9c5:	0f ae f8             	sfence
          if (waiting == 0) {
    d9c8:	8b 44 24 10          	mov    0x10(%rsp),%eax
    d9cc:	85 c0                	test   %eax,%eax
    d9ce:	0f 84 cc 00 00 00    	je     daa0 <barriered_thread+0x620>
        int arrived = 0; 
    d9d4:	c7 44 24 10 01 00 00 00 	movl   $0x1,0x10(%rsp)
    d9dc:	e9 d4 fb ff ff       	jmp    d5b5 <barriered_thread+0x135>
    d9e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          if (waiting == 1) {
    d9e8:	83 7c 24 10 01       	cmpl   $0x1,0x10(%rsp)
    d9ed:	0f 84 cd 01 00 00    	je     dbc0 <barriered_thread+0x740>
        int arrived = 0; 
    d9f3:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
    d9fb:	e9 bf fd ff ff       	jmp    d7bf <barriered_thread+0x33f>
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    da00:	48 8d 93 80 00 00 00 	lea    0x80(%rbx),%rdx
    da07:	49 89 d6             	mov    %rdx,%r14
    da0a:	49 c1 ee 03          	shr    $0x3,%r14
    da0e:	41 80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r14)
    da16:	0f 85 79 04 00 00    	jne    de95 <barriered_thread+0xa15>
    da1c:	48 8d bb 88 00 00 00 	lea    0x88(%rbx),%rdi
    da23:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    da2a:	48 89 f8             	mov    %rdi,%rax
    da2d:	48 c1 e8 03          	shr    $0x3,%rax
    da31:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    da38:	0f 85 52 04 00 00    	jne    de90 <barriered_thread+0xa10>
    da3e:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    da45:	0f 8d 7a ff ff ff    	jge    d9c5 <barriered_thread+0x545>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    da4b:	48 8d 7b 70          	lea    0x70(%rbx),%rdi
    da4f:	48 89 f8             	mov    %rdi,%rax
    da52:	48 c1 e8 03          	shr    $0x3,%rax
    da56:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    da5d:	0f 85 b2 03 00 00    	jne    de15 <barriered_thread+0x995>
    da63:	48 c1 e6 04          	shl    $0x4,%rsi
    da67:	bf 04 00 00 00       	mov    $0x4,%edi
    da6c:	48 03 73 70          	add    0x70(%rbx),%rsi
    da70:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    da75:	e8 06 6a ff ff       	call   4480 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    da7a:	41 80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r14)
    da82:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    da87:	0f 85 80 03 00 00    	jne    de0d <barriered_thread+0x98d>
    da8d:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    da95:	e9 2b ff ff ff       	jmp    d9c5 <barriered_thread+0x545>
    da9a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    daa0:	48 8d bb 90 00 00 00 	lea    0x90(%rbx),%rdi
    daa7:	48 89 f8             	mov    %rdi,%rax
    daaa:	48 c1 e8 03          	shr    $0x3,%rax
    daae:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    dab5:	0f 85 4d 03 00 00    	jne    de08 <barriered_thread+0x988>
    dabb:	48 8d bb 98 00 00 00 	lea    0x98(%rbx),%rdi
    dac2:	48 8b 93 90 00 00 00 	mov    0x90(%rbx),%rdx
    dac9:	48 89 f8             	mov    %rdi,%rax
    dacc:	48 c1 e8 03          	shr    $0x3,%rax
    dad0:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    dad7:	0f 85 26 03 00 00    	jne    de03 <barriered_thread+0x983>
    dadd:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    dae4:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    dae8:	48 8d 34 c2          	lea    (%rdx,%rax,8),%rsi
    daec:	48 8d 7e 20          	lea    0x20(%rsi),%rdi
    daf0:	48 89 f8             	mov    %rdi,%rax
    daf3:	48 c1 e8 03          	shr    $0x3,%rax
    daf7:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    dafe:	84 c0                	test   %al,%al
    db00:	74 08                	je     db0a <barriered_thread+0x68a>
    db02:	3c 03                	cmp    $0x3,%al
    db04:	0f 8e c8 03 00 00    	jle    ded2 <barriered_thread+0xa52>
    db0a:	44 89 6e 20          	mov    %r13d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    db0e:	bf 04 00 00 00       	mov    $0x4,%edi
    db13:	e8 68 69 ff ff       	call   4480 <clock_gettime@plt>
            waiting = 1;
    db18:	e9 b7 fe ff ff       	jmp    d9d4 <barriered_thread+0x554>
    db1d:	0f 1f 00             	nopl   (%rax)
  while (data->running == 1) {
    db20:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    db25:	48 c1 e8 03          	shr    $0x3,%rax
    db29:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    db30:	38 44 24 3f          	cmp    %al,0x3f(%rsp)
    db34:	7c 08                	jl     db3e <barriered_thread+0x6be>
    db36:	84 c0                	test   %al,%al
    db38:	0f 85 8a 03 00 00    	jne    dec8 <barriered_thread+0xa48>
    db3e:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    db42:	0f 84 c8 f9 ff ff    	je     d510 <barriered_thread+0x90>
}
    db48:	48 83 c4 48          	add    $0x48,%rsp
    db4c:	31 c0                	xor    %eax,%eax
    db4e:	5b                   	pop    %rbx
    db4f:	5d                   	pop    %rbp
    db50:	41 5c                	pop    %r12
    db52:	41 5d                	pop    %r13
    db54:	41 5e                	pop    %r14
    db56:	41 5f                	pop    %r15
    db58:	c3                   	ret
    db59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    db60:	48 8d 7b 68          	lea    0x68(%rbx),%rdi
    db64:	48 89 f8             	mov    %rdi,%rax
    db67:	48 c1 e8 03          	shr    $0x3,%rax
    db6b:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    db72:	0f 85 4b 03 00 00    	jne    dec3 <barriered_thread+0xa43>
    db78:	48 c1 e6 04          	shl    $0x4,%rsi
    db7c:	bf 04 00 00 00       	mov    $0x4,%edi
    db81:	48 03 73 68          	add    0x68(%rbx),%rsi
    db85:	e8 f6 68 ff ff       	call   4480 <clock_gettime@plt>
          data->tasks[t].available = 0;
    db8a:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    db8f:	48 c1 e8 03          	shr    $0x3,%rax
    db93:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    db9a:	0f 85 19 03 00 00    	jne    deb9 <barriered_thread+0xa39>
    dba0:	48 8b 43 38          	mov    0x38(%rbx),%rax
    dba4:	4c 01 e0             	add    %r12,%rax
    dba7:	e9 ca fc ff ff       	jmp    d876 <barriered_thread+0x3f6>
    dbac:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    dbb0:	83 7c 24 10 01       	cmpl   $0x1,0x10(%rsp)
    dbb5:	0f 85 2f fc ff ff    	jne    d7ea <barriered_thread+0x36a>
        int arrived = 0; 
    dbbb:	45 31 f6             	xor    %r14d,%r14d
    dbbe:	66 90                	xchg   %ax,%ax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    dbc0:	48 8d bb 90 00 00 00 	lea    0x90(%rbx),%rdi
    dbc7:	48 89 f8             	mov    %rdi,%rax
    dbca:	48 c1 e8 03          	shr    $0x3,%rax
    dbce:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    dbd5:	0f 85 d9 02 00 00    	jne    deb4 <barriered_thread+0xa34>
    dbdb:	48 8d 83 98 00 00 00 	lea    0x98(%rbx),%rax
    dbe2:	48 8b b3 90 00 00 00 	mov    0x90(%rbx),%rsi
    dbe9:	48 89 c1             	mov    %rax,%rcx
    dbec:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    dbf1:	48 c1 e9 03          	shr    $0x3,%rcx
    dbf5:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    dbfc:	0f 85 aa 02 00 00    	jne    deac <barriered_thread+0xa2c>
    dc02:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    dc09:	bf 04 00 00 00       	mov    $0x4,%edi
    dc0e:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    dc13:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    dc17:	48 8d 74 c6 10       	lea    0x10(%rsi,%rax,8),%rsi
    dc1c:	e8 5f 68 ff ff       	call   4480 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    dc21:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    dc26:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    dc2d:	0f 85 6f 02 00 00    	jne    dea2 <barriered_thread+0xa22>
    dc33:	48 8d bb a0 00 00 00 	lea    0xa0(%rbx),%rdi
    dc3a:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    dc41:	48 89 fa             	mov    %rdi,%rdx
    dc44:	48 c1 ea 03          	shr    $0x3,%rdx
    dc48:	48 83 c0 01          	add    $0x1,%rax
    dc4c:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    dc53:	0f 85 44 02 00 00    	jne    de9d <barriered_thread+0xa1d>
    dc59:	48 99                	cqto
    dc5b:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    dc62:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    dc69:	e9 85 fd ff ff       	jmp    d9f3 <barriered_thread+0x573>
    dc6e:	66 90                	xchg   %ax,%ax
    dc70:	48 8d bb a8 00 00 00 	lea    0xa8(%rbx),%rdi
      data->cycles++;
    dc77:	48 89 f8             	mov    %rdi,%rax
    dc7a:	48 c1 e8 03          	shr    $0x3,%rax
    dc7e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    dc85:	0f 85 cc 01 00 00    	jne    de57 <barriered_thread+0x9d7>
    dc8b:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    dc93:	85 d2                	test   %edx,%edx
    dc95:	0f 8e 8a 00 00 00    	jle    dd25 <barriered_thread+0x8a5>
    dc9b:	45 31 ed             	xor    %r13d,%r13d
    dc9e:	e9 76 f8 ff ff       	jmp    d519 <barriered_thread+0x99>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    dca3:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    dca7:	48 89 f8             	mov    %rdi,%rax
    dcaa:	48 c1 e8 03          	shr    $0x3,%rax
    dcae:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    dcb5:	0f 85 97 01 00 00    	jne    de52 <barriered_thread+0x9d2>
    dcbb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    dcc0:	48 8b 53 18          	mov    0x18(%rbx),%rdx
    dcc4:	48 c1 e8 03          	shr    $0x3,%rax
    dcc8:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    dccf:	38 44 24 3e          	cmp    %al,0x3e(%rsp)
    dcd3:	7c 08                	jl     dcdd <barriered_thread+0x85d>
    dcd5:	84 c0                	test   %al,%al
    dcd7:	0f 85 8e 01 00 00    	jne    de6b <barriered_thread+0x9eb>
    dcdd:	48 63 43 04          	movslq 0x4(%rbx),%rax
    dce1:	48 8d 3c c2          	lea    (%rdx,%rax,8),%rdi
    dce5:	48 89 f8             	mov    %rdi,%rax
    dce8:	48 c1 e8 03          	shr    $0x3,%rax
    dcec:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    dcf3:	0f 85 6d 01 00 00    	jne    de66 <barriered_thread+0x9e6>
    dcf9:	48 8b 07             	mov    (%rdi),%rax
    dcfc:	48 8d 78 38          	lea    0x38(%rax),%rdi
    dd00:	48 89 fa             	mov    %rdi,%rdx
    dd03:	48 c1 ea 03          	shr    $0x3,%rdx
    dd07:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    dd0e:	0f 85 29 01 00 00    	jne    de3d <barriered_thread+0x9bd>
    dd14:	48 8b 78 38          	mov    0x38(%rax),%rdi
    dd18:	4c 01 e7             	add    %r12,%rdi
    dd1b:	e8 60 f3 ff ff       	call   d080 <barriered_work_ingest>
          break;
    dd20:	e9 a1 f7 ff ff       	jmp    d4c6 <barriered_thread+0x46>
  while (data->running == 1) {
    dd25:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
    dd2a:	4c 89 d1             	mov    %r10,%rcx
    dd2d:	48 c1 e9 03          	shr    $0x3,%rcx
    dd31:	0f b6 b1 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%esi
    dd38:	4c 89 d1             	mov    %r10,%rcx
    dd3b:	83 e1 07             	and    $0x7,%ecx
    dd3e:	83 c1 03             	add    $0x3,%ecx
    dd41:	40 38 f1             	cmp    %sil,%cl
    dd44:	7c 09                	jl     dd4f <barriered_thread+0x8cf>
    dd46:	40 84 f6             	test   %sil,%sil
    dd49:	0f 85 31 01 00 00    	jne    de80 <barriered_thread+0xa00>
    dd4f:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    dd53:	0f 84 25 ff ff ff    	je     dc7e <barriered_thread+0x7fe>
    dd59:	e9 ea fd ff ff       	jmp    db48 <barriered_thread+0x6c8>
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    dd5e:	4c 89 df             	mov    %r11,%rdi
    dd61:	e8 ea 67 ff ff       	call   4550 <__asan_report_load4@plt>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    dd66:	4c 89 df             	mov    %r11,%rdi
    dd69:	e8 e2 67 ff ff       	call   4550 <__asan_report_load4@plt>
    dd6e:	48 89 cf             	mov    %rcx,%rdi
    dd71:	e8 6a 67 ff ff       	call   44e0 <__asan_report_load8@plt>
    dd76:	e8 65 67 ff ff       	call   44e0 <__asan_report_load8@plt>
    for (; t < data->task_count; t++) {
    dd7b:	4c 89 ff             	mov    %r15,%rdi
    dd7e:	e8 cd 67 ff ff       	call   4550 <__asan_report_load4@plt>
      if (data->tasks[t].available == 1) {
    dd83:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    dd88:	e8 53 67 ff ff       	call   44e0 <__asan_report_load8@plt>
    dd8d:	e8 be 67 ff ff       	call   4550 <__asan_report_load4@plt>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    dd92:	e8 49 67 ff ff       	call   44e0 <__asan_report_load8@plt>
    dd97:	e8 44 67 ff ff       	call   44e0 <__asan_report_load8@plt>
    dd9c:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    dda1:	e8 aa 67 ff ff       	call   4550 <__asan_report_load4@plt>
    dda6:	e8 35 67 ff ff       	call   44e0 <__asan_report_load8@plt>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    ddab:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    ddb0:	e8 9b 67 ff ff       	call   4550 <__asan_report_load4@plt>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    ddb5:	e8 26 67 ff ff       	call   44e0 <__asan_report_load8@plt>
    ddba:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    ddbf:	e8 8c 67 ff ff       	call   4550 <__asan_report_load4@plt>
    ddc4:	e8 17 67 ff ff       	call   44e0 <__asan_report_load8@plt>
          data->tasks[t].prearrive++;
    ddc9:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    ddce:	e8 0d 67 ff ff       	call   44e0 <__asan_report_load8@plt>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    ddd3:	e8 08 67 ff ff       	call   44e0 <__asan_report_load8@plt>
          data->tasks[t].available = 0;
    ddd8:	e8 e3 68 ff ff       	call   46c0 <__asan_report_store4@plt>
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    dddd:	4c 89 ff             	mov    %r15,%rdi
    dde0:	e8 6b 67 ff ff       	call   4550 <__asan_report_load4@plt>
          data->iteration_count++;
    dde5:	e8 f6 66 ff ff       	call   44e0 <__asan_report_load8@plt>
          data->tasks[t].arrived++;
    ddea:	e8 61 67 ff ff       	call   4550 <__asan_report_load4@plt>
    ddef:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    ddf4:	e8 e7 66 ff ff       	call   44e0 <__asan_report_load8@plt>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    ddf9:	e8 e2 66 ff ff       	call   44e0 <__asan_report_load8@plt>
          data->tasks[t].prearrive++;
    ddfe:	e8 4d 67 ff ff       	call   4550 <__asan_report_load4@plt>
            data->task_snapshot[data->task_timestamp_count].task = t;
    de03:	e8 d8 66 ff ff       	call   44e0 <__asan_report_load8@plt>
    de08:	e8 d3 66 ff ff       	call   44e0 <__asan_report_load8@plt>
            data->timestamp_count = data->timestamp_count + 1;
    de0d:	48 89 d7             	mov    %rdx,%rdi
    de10:	e8 cb 66 ff ff       	call   44e0 <__asan_report_load8@plt>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    de15:	e8 c6 66 ff ff       	call   44e0 <__asan_report_load8@plt>
    if (t >= data->task_count) {
    de1a:	4c 89 ff             	mov    %r15,%rdi
    de1d:	e8 2e 67 ff ff       	call   4550 <__asan_report_load4@plt>
  while (data->running == 1) {
    de22:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    de27:	e8 24 67 ff ff       	call   4550 <__asan_report_load4@plt>
    de2c:	0f 1f 40 00          	nopl   0x0(%rax)
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    de30:	4c 89 c7             	mov    %r8,%rdi
    de33:	e8 18 67 ff ff       	call   4550 <__asan_report_load4@plt>
    de38:	e8 a3 66 ff ff       	call   44e0 <__asan_report_load8@plt>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    de3d:	e8 9e 66 ff ff       	call   44e0 <__asan_report_load8@plt>
    de42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        if (arrived == 0 || arrived == data->thread_count) {
    de48:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    de4d:	e8 fe 66 ff ff       	call   4550 <__asan_report_load4@plt>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    de52:	e8 89 66 ff ff       	call   44e0 <__asan_report_load8@plt>
      data->cycles++;
    de57:	e8 84 66 ff ff       	call   44e0 <__asan_report_load8@plt>
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    de5c:	e8 7f 66 ff ff       	call   44e0 <__asan_report_load8@plt>
    de61:	e8 7a 66 ff ff       	call   44e0 <__asan_report_load8@plt>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    de66:	e8 75 66 ff ff       	call   44e0 <__asan_report_load8@plt>
    de6b:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    de70:	e8 db 66 ff ff       	call   4550 <__asan_report_load4@plt>
    de75:	0f 1f 00             	nopl   (%rax)
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    de78:	4c 89 c7             	mov    %r8,%rdi
    de7b:	e8 d0 66 ff ff       	call   4550 <__asan_report_load4@plt>
  while (data->running == 1) {
    de80:	4c 89 d7             	mov    %r10,%rdi
    de83:	e8 c8 66 ff ff       	call   4550 <__asan_report_load4@plt>
    de88:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    de90:	e8 4b 66 ff ff       	call   44e0 <__asan_report_load8@plt>
    de95:	48 89 d7             	mov    %rdx,%rdi
    de98:	e8 43 66 ff ff       	call   44e0 <__asan_report_load8@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    de9d:	e8 3e 66 ff ff       	call   44e0 <__asan_report_load8@plt>
    dea2:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    dea7:	e8 34 66 ff ff       	call   44e0 <__asan_report_load8@plt>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    deac:	48 89 c7             	mov    %rax,%rdi
    deaf:	e8 2c 66 ff ff       	call   44e0 <__asan_report_load8@plt>
    deb4:	e8 27 66 ff ff       	call   44e0 <__asan_report_load8@plt>
          data->tasks[t].available = 0;
    deb9:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    debe:	e8 1d 66 ff ff       	call   44e0 <__asan_report_load8@plt>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    dec3:	e8 18 66 ff ff       	call   44e0 <__asan_report_load8@plt>
  while (data->running == 1) {
    dec8:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    decd:	e8 7e 66 ff ff       	call   4550 <__asan_report_load4@plt>
            data->task_snapshot[data->task_timestamp_count].task = t;
    ded2:	e8 e9 67 ff ff       	call   46c0 <__asan_report_store4@plt>
    ded7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

000000000000dee0 <receive>:
int receive(struct BarrierTask *data) {
    dee0:	f3 0f 1e fa          	endbr64
    dee4:	41 57                	push   %r15
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    dee6:	48 8d 87 40 01 00 00 	lea    0x140(%rdi),%rax
int receive(struct BarrierTask *data) {
    deed:	41 56                	push   %r14
    deef:	41 55                	push   %r13
    def1:	41 54                	push   %r12
    def3:	55                   	push   %rbp
    def4:	53                   	push   %rbx
    def5:	48 89 fb             	mov    %rdi,%rbx
    def8:	48 83 ec 38          	sub    $0x38,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    defc:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    df01:	48 c1 e8 03          	shr    $0x3,%rax
    df05:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    df0c:	84 c0                	test   %al,%al
    df0e:	74 08                	je     df18 <receive+0x38>
    df10:	3c 03                	cmp    $0x3,%al
    df12:	0f 8e c9 03 00 00    	jle    e2e1 <receive+0x401>
    df18:	8b 8b 40 01 00 00    	mov    0x140(%rbx),%ecx
    df1e:	48 8d 83 70 01 00 00 	lea    0x170(%rbx),%rax
    df25:	45 31 ed             	xor    %r13d,%r13d
    df28:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    df2d:	85 c9                	test   %ecx,%ecx
    df2f:	0f 8e ac 02 00 00    	jle    e1e1 <receive+0x301>
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    df35:	48 8d 53 04          	lea    0x4(%rbx),%rdx
    struct Data *me = data->mailboxes[n].lower;
    df39:	49 89 c7             	mov    %rax,%r15
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    df3c:	48 89 d0             	mov    %rdx,%rax
    struct Data *me = data->mailboxes[n].lower;
    df3f:	49 c1 ef 03          	shr    $0x3,%r15
    df43:	49 89 d1             	mov    %rdx,%r9
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    df46:	83 e0 07             	and    $0x7,%eax
    df49:	4c 89 fa             	mov    %r15,%rdx
    df4c:	83 c0 03             	add    $0x3,%eax
    df4f:	88 44 24 17          	mov    %al,0x17(%rsp)
    df53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    struct Data *me = data->mailboxes[n].lower;
    df58:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    df5f:	0f 85 d1 03 00 00    	jne    e336 <receive+0x456>
    df65:	4c 8b 83 70 01 00 00 	mov    0x170(%rbx),%r8
    df6c:	4b 8d 6c ad 00       	lea    0x0(%r13,%r13,4),%rbp
    df71:	48 c1 e5 03          	shl    $0x3,%rbp
    df75:	49 01 e8             	add    %rbp,%r8
    df78:	4c 89 c0             	mov    %r8,%rax
    df7b:	48 c1 e8 03          	shr    $0x3,%rax
    df7f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    df86:	0f 85 a2 03 00 00    	jne    e32e <receive+0x44e>
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    df8c:	49 8d 78 20          	lea    0x20(%r8),%rdi
    struct Data *me = data->mailboxes[n].lower;
    df90:	4d 8b 20             	mov    (%r8),%r12
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    df93:	48 89 f8             	mov    %rdi,%rax
    df96:	48 c1 e8 03          	shr    $0x3,%rax
    df9a:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    dfa1:	84 c0                	test   %al,%al
    dfa3:	74 08                	je     dfad <receive+0xcd>
    dfa5:	3c 03                	cmp    $0x3,%al
    dfa7:	0f 8e 60 03 00 00    	jle    e30d <receive+0x42d>
    dfad:	41 83 78 20 02       	cmpl   $0x2,0x20(%r8)
    dfb2:	0f 84 40 02 00 00    	je     e1f8 <receive+0x318>
    for (int x = 0 ; x < me->messages_count ; x++) {
    dfb8:	49 8d 7c 24 08       	lea    0x8(%r12),%rdi
    dfbd:	48 89 f8             	mov    %rdi,%rax
    dfc0:	48 c1 e8 03          	shr    $0x3,%rax
    dfc4:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    dfcb:	0f 85 37 03 00 00    	jne    e308 <receive+0x428>
    dfd1:	4d 8b 54 24 08       	mov    0x8(%r12),%r10
    dfd6:	4d 85 d2             	test   %r10,%r10
    dfd9:	0f 8e 9e 01 00 00    	jle    e17d <receive+0x29d>
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    dfdf:	4c 89 e0             	mov    %r12,%rax
    dfe2:	48 c1 e8 03          	shr    $0x3,%rax
    dfe6:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    dfed:	0f 85 d6 02 00 00    	jne    e2c9 <receive+0x3e9>
    dff3:	4c 89 c8             	mov    %r9,%rax
    dff6:	49 8b 3c 24          	mov    (%r12),%rdi
    dffa:	48 c1 e8 03          	shr    $0x3,%rax
    dffe:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e005:	38 44 24 17          	cmp    %al,0x17(%rsp)
    e009:	7c 08                	jl     e013 <receive+0x133>
    e00b:	84 c0                	test   %al,%al
    e00d:	0f 85 be 02 00 00    	jne    e2d1 <receive+0x3f1>
      data->sends++;
    e013:	48 8d 83 78 01 00 00 	lea    0x178(%rbx),%rax
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    e01a:	4c 63 73 04          	movslq 0x4(%rbx),%r14
      data->sends++;
    e01e:	48 89 c1             	mov    %rax,%rcx
    e021:	48 c1 e9 03          	shr    $0x3,%rcx
    e025:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    e02c:	0f 85 ce 02 00 00    	jne    e300 <receive+0x420>
      data->n++;
    e032:	48 8d 83 08 01 00 00 	lea    0x108(%rbx),%rax
      data->sends++;
    e039:	48 8b 8b 78 01 00 00 	mov    0x178(%rbx),%rcx
      data->n++;
    e040:	48 89 c6             	mov    %rax,%rsi
    e043:	48 c1 ee 03          	shr    $0x3,%rsi
    e047:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    e04e:	0f 85 85 02 00 00    	jne    e2d9 <receive+0x3f9>
      data->mailboxes[n].received++;
    e054:	49 8d 40 18          	lea    0x18(%r8),%rax
      data->n++;
    e058:	48 8b ab 08 01 00 00 	mov    0x108(%rbx),%rbp
      data->mailboxes[n].received++;
    e05f:	48 89 c6             	mov    %rax,%rsi
    e062:	48 c1 ee 03          	shr    $0x3,%rsi
    e066:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    e06d:	0f 85 9f 02 00 00    	jne    e312 <receive+0x432>
    e073:	4d 8b 58 18          	mov    0x18(%r8),%r11
    e077:	48 8d 41 01          	lea    0x1(%rcx),%rax
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    e07b:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
      data->n++;
    e080:	48 29 cd             	sub    %rcx,%rbp
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    e083:	48 8d b3 30 01 00 00 	lea    0x130(%rbx),%rsi
    e08a:	49 01 c2             	add    %rax,%r10
    e08d:	49 89 f7             	mov    %rsi,%r15
    e090:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
      data->mailboxes[n].received++;
    e095:	49 29 cb             	sub    %rcx,%r11
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    e098:	49 c1 ef 03          	shr    $0x3,%r15
    e09c:	eb 13                	jmp    e0b1 <receive+0x1d1>
    e09e:	66 90                	xchg   %ax,%ax
    for (int x = 0 ; x < me->messages_count ; x++) {
    e0a0:	48 83 c0 01          	add    $0x1,%rax
    e0a4:	48 83 c7 08          	add    $0x8,%rdi
    e0a8:	4c 39 d0             	cmp    %r10,%rax
    e0ab:	0f 84 c7 00 00 00    	je     e178 <receive+0x298>
      data->n++;
    e0b1:	48 8d 4c 05 00       	lea    0x0(%rbp,%rax,1),%rcx
      data->sends++;
    e0b6:	48 89 83 78 01 00 00 	mov    %rax,0x178(%rbx)
      data->n++;
    e0bd:	48 89 8b 08 01 00 00 	mov    %rcx,0x108(%rbx)
      data->mailboxes[n].received++;
    e0c4:	49 8d 0c 03          	lea    (%r11,%rax,1),%rcx
    e0c8:	49 89 48 18          	mov    %rcx,0x18(%r8)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    e0cc:	48 89 f9             	mov    %rdi,%rcx
    e0cf:	48 c1 e9 03          	shr    $0x3,%rcx
    e0d3:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    e0da:	0f 85 ca 01 00 00    	jne    e2aa <receive+0x3ca>
    e0e0:	48 8b 37             	mov    (%rdi),%rsi
    e0e3:	48 8d 4e 10          	lea    0x10(%rsi),%rcx
    e0e7:	49 89 cc             	mov    %rcx,%r12
    e0ea:	49 c1 ec 03          	shr    $0x3,%r12
    e0ee:	41 80 bc 24 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r12)
    e0f7:	0f 85 b2 01 00 00    	jne    e2af <receive+0x3cf>
    e0fd:	4c 39 76 10          	cmp    %r14,0x10(%rsi)
    e101:	75 9d                	jne    e0a0 <receive+0x1c0>
    e103:	48 8d 4e 08          	lea    0x8(%rsi),%rcx
    e107:	49 89 cc             	mov    %rcx,%r12
    e10a:	49 c1 ec 03          	shr    $0x3,%r12
    e10e:	41 80 bc 24 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r12)
    e117:	0f 85 a4 01 00 00    	jne    e2c1 <receive+0x3e1>
    e11d:	41 0f b6 8f 00 80 ff 7f 	movzbl 0x7fff8000(%r15),%ecx
    e125:	48 8b 76 08          	mov    0x8(%rsi),%rsi
    e129:	84 c9                	test   %cl,%cl
    e12b:	74 09                	je     e136 <receive+0x256>
    e12d:	80 f9 03             	cmp    $0x3,%cl
    e130:	0f 8e 81 01 00 00    	jle    e2b7 <receive+0x3d7>
    e136:	48 63 8b 30 01 00 00 	movslq 0x130(%rbx),%rcx
    e13d:	48 39 ce             	cmp    %rcx,%rsi
    e140:	0f 85 5a ff ff ff    	jne    e0a0 <receive+0x1c0>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    e146:	bf 01 00 00 00       	mov    $0x1,%edi
    e14b:	b9 01 00 00 00       	mov    $0x1,%ecx
    e150:	ba 01 00 00 00       	mov    $0x1,%edx
    e155:	31 c0                	xor    %eax,%eax
    e157:	48 8d 35 c2 2c 00 00 	lea    0x2cc2(%rip),%rsi        # 10e20 <_IO_stdin_used+0xe20>
    e15e:	e8 bd 63 ff ff       	call   4520 <__printf_chk@plt>
        exit(1);
    e163:	e8 a8 64 ff ff       	call   4610 <__asan_handle_no_return@plt>
    e168:	bf 01 00 00 00       	mov    $0x1,%edi
    e16d:	e8 9e 63 ff ff       	call   4510 <exit@plt>
    e172:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    e178:	4c 8b 64 24 08       	mov    0x8(%rsp),%r12
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    e17d:	49 8d 78 20          	lea    0x20(%r8),%rdi
    e181:	48 89 f8             	mov    %rdi,%rax
    e184:	48 c1 e8 03          	shr    $0x3,%rax
    e188:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e18f:	84 c0                	test   %al,%al
    e191:	74 08                	je     e19b <receive+0x2bb>
    e193:	3c 03                	cmp    $0x3,%al
    e195:	0f 8e 8e 01 00 00    	jle    e329 <receive+0x449>
    e19b:	41 83 78 20 02       	cmpl   $0x2,0x20(%r8)
    e1a0:	0f 84 8a 00 00 00    	je     e230 <receive+0x350>
    me->messages_count = 0;
    e1a6:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    asm volatile ("sfence" ::: "memory");
    e1af:	0f ae f8             	sfence
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    e1b2:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    e1b7:	48 c1 e8 03          	shr    $0x3,%rax
    e1bb:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e1c2:	84 c0                	test   %al,%al
    e1c4:	74 08                	je     e1ce <receive+0x2ee>
    e1c6:	3c 03                	cmp    $0x3,%al
    e1c8:	0f 8e 51 01 00 00    	jle    e31f <receive+0x43f>
    e1ce:	8b 8b 40 01 00 00    	mov    0x140(%rbx),%ecx
    e1d4:	49 83 c5 01          	add    $0x1,%r13
    e1d8:	44 39 e9             	cmp    %r13d,%ecx
    e1db:	0f 8f 77 fd ff ff    	jg     df58 <receive+0x78>
}
    e1e1:	48 83 c4 38          	add    $0x38,%rsp
    e1e5:	31 c0                	xor    %eax,%eax
    e1e7:	5b                   	pop    %rbx
    e1e8:	5d                   	pop    %rbp
    e1e9:	41 5c                	pop    %r12
    e1eb:	41 5d                	pop    %r13
    e1ed:	41 5e                	pop    %r14
    e1ef:	41 5f                	pop    %r15
    e1f1:	c3                   	ret
    e1f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    e1f8:	49 8d 7c 24 18       	lea    0x18(%r12),%rdi
    e1fd:	48 89 f8             	mov    %rdi,%rax
    e200:	48 c1 e8 03          	shr    $0x3,%rax
    e204:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e20b:	84 c0                	test   %al,%al
    e20d:	74 08                	je     e217 <receive+0x337>
    e20f:	3c 03                	cmp    $0x3,%al
    e211:	0f 8e 03 01 00 00    	jle    e31a <receive+0x43a>
    e217:	41 8b 44 24 18       	mov    0x18(%r12),%eax
    e21c:	83 f8 01             	cmp    $0x1,%eax
    e21f:	74 48                	je     e269 <receive+0x389>
    else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 0) {
    e221:	85 c0                	test   %eax,%eax
    e223:	74 af                	je     e1d4 <receive+0x2f4>
    e225:	e9 8e fd ff ff       	jmp    dfb8 <receive+0xd8>
    e22a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    e230:	49 8d 7c 24 18       	lea    0x18(%r12),%rdi
    e235:	48 89 f8             	mov    %rdi,%rax
    e238:	48 c1 e8 03          	shr    $0x3,%rax
    e23c:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e243:	84 c0                	test   %al,%al
    e245:	74 08                	je     e24f <receive+0x36f>
    e247:	3c 03                	cmp    $0x3,%al
    e249:	0f 8e 9c 00 00 00    	jle    e2eb <receive+0x40b>
    e24f:	41 83 7c 24 18 01    	cmpl   $0x1,0x18(%r12)
    e255:	0f 85 4b ff ff ff    	jne    e1a6 <receive+0x2c6>
      me->available = 0;
    e25b:	41 c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%r12)
    e264:	e9 3d ff ff ff       	jmp    e1a6 <receive+0x2c6>
    e269:	48 8d 3d 50 2b 00 00 	lea    0x2b50(%rip),%rdi        # 10dc0 <_IO_stdin_used+0xdc0>
    e270:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    e275:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
    e27a:	e8 81 65 ff ff       	call   4800 <puts@plt>
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    e27f:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    e284:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    e289:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    e28e:	48 c1 e8 03          	shr    $0x3,%rax
    e292:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e299:	75 55                	jne    e2f0 <receive+0x410>
    e29b:	4c 8b 83 70 01 00 00 	mov    0x170(%rbx),%r8
    e2a2:	49 01 e8             	add    %rbp,%r8
    e2a5:	e9 0e fd ff ff       	jmp    dfb8 <receive+0xd8>
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    e2aa:	e8 31 62 ff ff       	call   44e0 <__asan_report_load8@plt>
    e2af:	48 89 cf             	mov    %rcx,%rdi
    e2b2:	e8 29 62 ff ff       	call   44e0 <__asan_report_load8@plt>
    e2b7:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    e2bc:	e8 8f 62 ff ff       	call   4550 <__asan_report_load4@plt>
    e2c1:	48 89 cf             	mov    %rcx,%rdi
    e2c4:	e8 17 62 ff ff       	call   44e0 <__asan_report_load8@plt>
    e2c9:	4c 89 e7             	mov    %r12,%rdi
    e2cc:	e8 0f 62 ff ff       	call   44e0 <__asan_report_load8@plt>
    e2d1:	4c 89 cf             	mov    %r9,%rdi
    e2d4:	e8 77 62 ff ff       	call   4550 <__asan_report_load4@plt>
      data->n++;
    e2d9:	48 89 c7             	mov    %rax,%rdi
    e2dc:	e8 ff 61 ff ff       	call   44e0 <__asan_report_load8@plt>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    e2e1:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    e2e6:	e8 65 62 ff ff       	call   4550 <__asan_report_load4@plt>
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    e2eb:	e8 60 62 ff ff       	call   4550 <__asan_report_load4@plt>
    e2f0:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    e2f5:	e8 e6 61 ff ff       	call   44e0 <__asan_report_load8@plt>
    e2fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->sends++;
    e300:	48 89 c7             	mov    %rax,%rdi
    e303:	e8 d8 61 ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int x = 0 ; x < me->messages_count ; x++) {
    e308:	e8 d3 61 ff ff       	call   44e0 <__asan_report_load8@plt>
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    e30d:	e8 3e 62 ff ff       	call   4550 <__asan_report_load4@plt>
      data->mailboxes[n].received++;
    e312:	48 89 c7             	mov    %rax,%rdi
    e315:	e8 c6 61 ff ff       	call   44e0 <__asan_report_load8@plt>
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    e31a:	e8 31 62 ff ff       	call   4550 <__asan_report_load4@plt>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    e31f:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    e324:	e8 27 62 ff ff       	call   4550 <__asan_report_load4@plt>
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    e329:	e8 22 62 ff ff       	call   4550 <__asan_report_load4@plt>
    struct Data *me = data->mailboxes[n].lower;
    e32e:	4c 89 c7             	mov    %r8,%rdi
    e331:	e8 aa 61 ff ff       	call   44e0 <__asan_report_load8@plt>
    e336:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    e33b:	e8 a0 61 ff ff       	call   44e0 <__asan_report_load8@plt>

000000000000e340 <sendm>:
int sendm(struct BarrierTask *data) {
    e340:	f3 0f 1e fa          	endbr64
    e344:	41 57                	push   %r15
    e346:	41 56                	push   %r14
    e348:	41 55                	push   %r13
    e34a:	41 54                	push   %r12
    e34c:	55                   	push   %rbp
    e34d:	53                   	push   %rbx
    e34e:	48 89 fb             	mov    %rdi,%rbx
  if (data->sending == 1) {
    e351:	48 81 c7 80 01 00 00 	add    $0x180,%rdi
    e358:	48 89 f8             	mov    %rdi,%rax
    e35b:	48 c1 e8 03          	shr    $0x3,%rax
int sendm(struct BarrierTask *data) {
    e35f:	48 83 ec 58          	sub    $0x58,%rsp
  if (data->sending == 1) {
    e363:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e36a:	84 c0                	test   %al,%al
    e36c:	74 08                	je     e376 <sendm+0x36>
    e36e:	3c 03                	cmp    $0x3,%al
    e370:	0f 8e 66 04 00 00    	jle    e7dc <sendm+0x49c>
    e376:	83 bb 80 01 00 00 01 	cmpl   $0x1,0x180(%rbx)
    e37d:	0f 85 6d 03 00 00    	jne    e6f0 <sendm+0x3b0>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    e383:	4c 8d a3 40 01 00 00 	lea    0x140(%rbx),%r12
    e38a:	4c 89 e0             	mov    %r12,%rax
    e38d:	48 c1 e8 03          	shr    $0x3,%rax
    e391:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e398:	84 c0                	test   %al,%al
    e39a:	74 08                	je     e3a4 <sendm+0x64>
    e39c:	3c 03                	cmp    $0x3,%al
    e39e:	0f 8e 63 04 00 00    	jle    e807 <sendm+0x4c7>
    e3a4:	8b 93 40 01 00 00    	mov    0x140(%rbx),%edx
    e3aa:	45 31 ed             	xor    %r13d,%r13d
    e3ad:	45 31 f6             	xor    %r14d,%r14d
    e3b0:	48 8d b3 30 01 00 00 	lea    0x130(%rbx),%rsi
    e3b7:	85 d2                	test   %edx,%edx
    e3b9:	0f 8e 58 02 00 00    	jle    e617 <sendm+0x2d7>
        if (n == data->thread_index) { continue; }
    e3bf:	48 89 f0             	mov    %rsi,%rax
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    e3c2:	4c 89 64 24 40       	mov    %r12,0x40(%rsp)
        if (n == data->thread_index) { continue; }
    e3c7:	48 c1 e8 03          	shr    $0x3,%rax
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    e3cb:	48 89 74 24 48       	mov    %rsi,0x48(%rsp)
        if (n == data->thread_index) { continue; }
    e3d0:	48 89 04 24          	mov    %rax,(%rsp)
        struct Data *them = data->mailboxes[n].higher;
    e3d4:	48 8d 83 70 01 00 00 	lea    0x170(%rbx),%rax
    e3db:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    e3e0:	48 c1 e8 03          	shr    $0x3,%rax
    e3e4:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    e3e9:	4c 89 e0             	mov    %r12,%rax
    e3ec:	48 c1 e8 03          	shr    $0x3,%rax
    e3f0:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    e3f5:	0f 1f 00             	nopl   (%rax)
        if (n == data->thread_index) { continue; }
    e3f8:	48 8b 04 24          	mov    (%rsp),%rax
    e3fc:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e403:	84 c0                	test   %al,%al
    e405:	74 08                	je     e40f <sendm+0xcf>
    e407:	3c 03                	cmp    $0x3,%al
    e409:	0f 8e a7 03 00 00    	jle    e7b6 <sendm+0x476>
    e40f:	44 39 b3 30 01 00 00 	cmp    %r14d,0x130(%rbx)
    e416:	0f 84 ea 01 00 00    	je     e606 <sendm+0x2c6>
        struct Data *them = data->mailboxes[n].higher;
    e41c:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    e421:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e428:	0f 85 92 03 00 00    	jne    e7c0 <sendm+0x480>
    e42e:	4c 8b 8b 70 01 00 00 	mov    0x170(%rbx),%r9
    e435:	4d 01 e9             	add    %r13,%r9
    e438:	49 8d 79 08          	lea    0x8(%r9),%rdi
    e43c:	48 89 f8             	mov    %rdi,%rax
    e43f:	48 c1 e8 03          	shr    $0x3,%rax
    e443:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e44a:	0f 85 5c 03 00 00    	jne    e7ac <sendm+0x46c>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    e450:	49 8d 79 20          	lea    0x20(%r9),%rdi
        struct Data *them = data->mailboxes[n].higher;
    e454:	49 8b 69 08          	mov    0x8(%r9),%rbp
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    e458:	48 89 f8             	mov    %rdi,%rax
    e45b:	48 c1 e8 03          	shr    $0x3,%rax
    e45f:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e466:	84 c0                	test   %al,%al
    e468:	74 08                	je     e472 <sendm+0x132>
    e46a:	3c 03                	cmp    $0x3,%al
    e46c:	0f 8e 3f 03 00 00    	jle    e7b1 <sendm+0x471>
    e472:	41 8b 71 20          	mov    0x20(%r9),%esi
    e476:	83 fe 02             	cmp    $0x2,%esi
    e479:	0f 84 b1 01 00 00    	je     e630 <sendm+0x2f0>
        int min = them->messages_limit;
    e47f:	48 8d 7d 10          	lea    0x10(%rbp),%rdi
    e483:	48 89 f8             	mov    %rdi,%rax
    e486:	48 c1 e8 03          	shr    $0x3,%rax
    e48a:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e491:	0f 85 59 03 00 00    	jne    e7f0 <sendm+0x4b0>
        for (; them->messages_count < min;) {
    e497:	4c 8d 7d 08          	lea    0x8(%rbp),%r15
        int min = them->messages_limit;
    e49b:	4c 8b 45 10          	mov    0x10(%rbp),%r8
        for (; them->messages_count < min;) {
    e49f:	4c 89 f8             	mov    %r15,%rax
    e4a2:	48 c1 e8 03          	shr    $0x3,%rax
        int min = them->messages_limit;
    e4a6:	49 63 c8             	movslq %r8d,%rcx
        for (; them->messages_count < min;) {
    e4a9:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e4b0:	0f 85 3f 03 00 00    	jne    e7f5 <sendm+0x4b5>
    e4b6:	48 8b 45 08          	mov    0x8(%rbp),%rax
    e4ba:	4d 63 c0             	movslq %r8d,%r8
    e4bd:	4c 39 c0             	cmp    %r8,%rax
    e4c0:	0f 8d 1f 01 00 00    	jge    e5e5 <sendm+0x2a5>
          data->n++;
    e4c6:	48 8d bb 08 01 00 00 	lea    0x108(%rbx),%rdi
    e4cd:	48 89 fa             	mov    %rdi,%rdx
    e4d0:	48 c1 ea 03          	shr    $0x3,%rdx
    e4d4:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    e4db:	0f 85 1c 03 00 00    	jne    e7fd <sendm+0x4bd>
    e4e1:	48 8b 93 08 01 00 00 	mov    0x108(%rbx),%rdx
          data->mailboxes[n].sent++;
    e4e8:	49 8d 79 10          	lea    0x10(%r9),%rdi
    e4ec:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
    e4f1:	48 89 fa             	mov    %rdi,%rdx
    e4f4:	48 c1 ea 03          	shr    $0x3,%rdx
    e4f8:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    e4ff:	0f 85 fd 02 00 00    	jne    e802 <sendm+0x4c2>
    e505:	49 8b 51 10          	mov    0x10(%r9),%rdx
    e509:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
          them->messages[them->messages_count++] = data->message; 
    e50e:	48 89 ea             	mov    %rbp,%rdx
    e511:	48 c1 ea 03          	shr    $0x3,%rdx
    e515:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    e51c:	0f 85 f2 02 00 00    	jne    e814 <sendm+0x4d4>
    e522:	48 8d 93 88 01 00 00 	lea    0x188(%rbx),%rdx
    e529:	4c 8b 65 00          	mov    0x0(%rbp),%r12
    e52d:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    e532:	49 89 c3             	mov    %rax,%r11
    e535:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
    e53a:	49 89 d2             	mov    %rdx,%r10
    e53d:	49 8d 3c c4          	lea    (%r12,%rax,8),%rdi
    e541:	49 c1 ea 03          	shr    $0x3,%r10
    e545:	0f 1f 00             	nopl   (%rax)
    e548:	48 83 c0 01          	add    $0x1,%rax
    e54c:	41 80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r10)
    e554:	0f 85 3e 02 00 00    	jne    e798 <sendm+0x458>
    e55a:	49 89 f9             	mov    %rdi,%r9
    e55d:	48 8b 93 88 01 00 00 	mov    0x188(%rbx),%rdx
    e564:	49 c1 e9 03          	shr    $0x3,%r9
    e568:	41 80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r9)
    e570:	0f 85 1d 02 00 00    	jne    e793 <sendm+0x453>
    e576:	48 89 17             	mov    %rdx,(%rdi)
        for (; them->messages_count < min;) {
    e579:	48 83 c7 08          	add    $0x8,%rdi
    e57d:	4c 39 c0             	cmp    %r8,%rax
    e580:	75 c6                	jne    e548 <sendm+0x208>
    e582:	49 89 c8             	mov    %rcx,%r8
    e585:	49 8d 7c cc f8       	lea    -0x8(%r12,%rcx,8),%rdi
    e58a:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    e58f:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    e594:	4d 29 d8             	sub    %r11,%r8
    e597:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    e59c:	4c 01 c1             	add    %r8,%rcx
    e59f:	48 89 8b 08 01 00 00 	mov    %rcx,0x108(%rbx)
          them->messages[them->messages_count++] = data->message; 
    e5a6:	4c 89 f9             	mov    %r15,%rcx
    e5a9:	4d 01 c3             	add    %r8,%r11
    e5ac:	48 c1 e9 03          	shr    $0x3,%rcx
    e5b0:	4d 89 59 10          	mov    %r11,0x10(%r9)
    e5b4:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    e5bb:	0f 85 5b 02 00 00    	jne    e81c <sendm+0x4dc>
    e5c1:	48 89 45 08          	mov    %rax,0x8(%rbp)
    e5c5:	48 89 f8             	mov    %rdi,%rax
    e5c8:	48 c1 e8 03          	shr    $0x3,%rax
    e5cc:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e5d3:	0f 85 08 02 00 00    	jne    e7e1 <sendm+0x4a1>
    e5d9:	48 89 17             	mov    %rdx,(%rdi)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    e5dc:	83 fe 02             	cmp    $0x2,%esi
    e5df:	0f 84 fb 00 00 00    	je     e6e0 <sendm+0x3a0>
        asm volatile ("sfence" ::: "memory");
    e5e5:	0f ae f8             	sfence
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    e5e8:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    e5ed:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e5f4:	84 c0                	test   %al,%al
    e5f6:	74 08                	je     e600 <sendm+0x2c0>
    e5f8:	3c 03                	cmp    $0x3,%al
    e5fa:	0f 8e a2 01 00 00    	jle    e7a2 <sendm+0x462>
    e600:	8b 93 40 01 00 00    	mov    0x140(%rbx),%edx
    e606:	41 83 c6 01          	add    $0x1,%r14d
    e60a:	49 83 c5 28          	add    $0x28,%r13
    e60e:	41 39 d6             	cmp    %edx,%r14d
    e611:	0f 8c e1 fd ff ff    	jl     e3f8 <sendm+0xb8>
}
    e617:	48 83 c4 58          	add    $0x58,%rsp
    e61b:	31 c0                	xor    %eax,%eax
    e61d:	5b                   	pop    %rbx
    e61e:	5d                   	pop    %rbp
    e61f:	41 5c                	pop    %r12
    e621:	41 5d                	pop    %r13
    e623:	41 5e                	pop    %r14
    e625:	41 5f                	pop    %r15
    e627:	c3                   	ret
    e628:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    e630:	48 8d 7d 18          	lea    0x18(%rbp),%rdi
    e634:	48 89 f8             	mov    %rdi,%rax
    e637:	48 c1 e8 03          	shr    $0x3,%rax
    e63b:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e642:	84 c0                	test   %al,%al
    e644:	74 08                	je     e64e <sendm+0x30e>
    e646:	3c 03                	cmp    $0x3,%al
    e648:	0f 8e c1 01 00 00    	jle    e80f <sendm+0x4cf>
    e64e:	8b 45 18             	mov    0x18(%rbp),%eax
    e651:	85 c0                	test   %eax,%eax
    e653:	0f 84 a8 00 00 00    	je     e701 <sendm+0x3c1>
        else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    e659:	83 f8 01             	cmp    $0x1,%eax
    e65c:	74 a8                	je     e606 <sendm+0x2c6>
        int min = them->messages_limit;
    e65e:	48 8d 45 10          	lea    0x10(%rbp),%rax
    e662:	48 89 c2             	mov    %rax,%rdx
    e665:	48 c1 ea 03          	shr    $0x3,%rdx
    e669:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    e670:	0f 85 ae 01 00 00    	jne    e824 <sendm+0x4e4>
        for (; them->messages_count < min;) {
    e676:	4c 8d 7d 08          	lea    0x8(%rbp),%r15
        int min = them->messages_limit;
    e67a:	4c 8b 45 10          	mov    0x10(%rbp),%r8
        for (; them->messages_count < min;) {
    e67e:	4c 89 f8             	mov    %r15,%rax
    e681:	48 c1 e8 03          	shr    $0x3,%rax
        int min = them->messages_limit;
    e685:	49 63 c8             	movslq %r8d,%rcx
        for (; them->messages_count < min;) {
    e688:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e68f:	0f 85 97 01 00 00    	jne    e82c <sendm+0x4ec>
    e695:	48 8b 45 08          	mov    0x8(%rbp),%rax
    e699:	4d 63 c0             	movslq %r8d,%r8
    e69c:	49 39 c0             	cmp    %rax,%r8
    e69f:	0f 8f 21 fe ff ff    	jg     e4c6 <sendm+0x186>
    e6a5:	0f 1f 00             	nopl   (%rax)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    e6a8:	48 89 f8             	mov    %rdi,%rax
    e6ab:	48 c1 e8 03          	shr    $0x3,%rax
    e6af:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e6b6:	84 c0                	test   %al,%al
    e6b8:	74 08                	je     e6c2 <sendm+0x382>
    e6ba:	3c 03                	cmp    $0x3,%al
    e6bc:	0f 8e 72 01 00 00    	jle    e834 <sendm+0x4f4>
    e6c2:	8b 45 18             	mov    0x18(%rbp),%eax
    e6c5:	85 c0                	test   %eax,%eax
    e6c7:	0f 85 18 ff ff ff    	jne    e5e5 <sendm+0x2a5>
          them->available = 1;
    e6cd:	c7 45 18 01 00 00 00 	movl   $0x1,0x18(%rbp)
    e6d4:	e9 0c ff ff ff       	jmp    e5e5 <sendm+0x2a5>
    e6d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    e6e0:	48 8d 7d 18          	lea    0x18(%rbp),%rdi
    e6e4:	eb c2                	jmp    e6a8 <sendm+0x368>
    e6e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    e6f0:	48 8d 3d e9 27 00 00 	lea    0x27e9(%rip),%rdi        # 10ee0 <_IO_stdin_used+0xee0>
    e6f7:	e8 04 61 ff ff       	call   4800 <puts@plt>
    e6fc:	e9 16 ff ff ff       	jmp    e617 <sendm+0x2d7>
    e701:	48 8d 3d 78 27 00 00 	lea    0x2778(%rip),%rdi        # 10e80 <_IO_stdin_used+0xe80>
    e708:	e8 f3 60 ff ff       	call   4800 <puts@plt>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    e70d:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    e712:	48 c1 e8 03          	shr    $0x3,%rax
    e716:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e71d:	0f 85 c3 00 00 00    	jne    e7e6 <sendm+0x4a6>
    e723:	4c 8b 8b 70 01 00 00 	mov    0x170(%rbx),%r9
    e72a:	4d 01 e9             	add    %r13,%r9
    e72d:	49 8d 79 20          	lea    0x20(%r9),%rdi
    e731:	48 89 f8             	mov    %rdi,%rax
    e734:	48 c1 e8 03          	shr    $0x3,%rax
    e738:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e73f:	84 c0                	test   %al,%al
    e741:	74 08                	je     e74b <sendm+0x40b>
    e743:	3c 03                	cmp    $0x3,%al
    e745:	0f 8e 8c 00 00 00    	jle    e7d7 <sendm+0x497>
        int min = them->messages_limit;
    e74b:	48 8d 7d 10          	lea    0x10(%rbp),%rdi
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    e74f:	41 8b 71 20          	mov    0x20(%r9),%esi
        int min = them->messages_limit;
    e753:	48 89 f8             	mov    %rdi,%rax
    e756:	48 c1 e8 03          	shr    $0x3,%rax
    e75a:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e761:	75 6f                	jne    e7d2 <sendm+0x492>
        for (; them->messages_count < min;) {
    e763:	4c 8d 7d 08          	lea    0x8(%rbp),%r15
        int min = them->messages_limit;
    e767:	4c 8b 45 10          	mov    0x10(%rbp),%r8
        for (; them->messages_count < min;) {
    e76b:	4c 89 f8             	mov    %r15,%rax
    e76e:	48 c1 e8 03          	shr    $0x3,%rax
        int min = them->messages_limit;
    e772:	49 63 c8             	movslq %r8d,%rcx
        for (; them->messages_count < min;) {
    e775:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e77c:	75 4c                	jne    e7ca <sendm+0x48a>
    e77e:	48 8b 45 08          	mov    0x8(%rbp),%rax
    e782:	4d 63 c0             	movslq %r8d,%r8
    e785:	4c 39 c0             	cmp    %r8,%rax
    e788:	0f 8c 38 fd ff ff    	jl     e4c6 <sendm+0x186>
    e78e:	e9 49 fe ff ff       	jmp    e5dc <sendm+0x29c>
          them->messages[them->messages_count++] = data->message; 
    e793:	e8 38 5f ff ff       	call   46d0 <__asan_report_store8@plt>
    e798:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    e79d:	e8 3e 5d ff ff       	call   44e0 <__asan_report_load8@plt>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    e7a2:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    e7a7:	e8 a4 5d ff ff       	call   4550 <__asan_report_load4@plt>
        struct Data *them = data->mailboxes[n].higher;
    e7ac:	e8 2f 5d ff ff       	call   44e0 <__asan_report_load8@plt>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    e7b1:	e8 9a 5d ff ff       	call   4550 <__asan_report_load4@plt>
        if (n == data->thread_index) { continue; }
    e7b6:	48 8b 7c 24 48       	mov    0x48(%rsp),%rdi
    e7bb:	e8 90 5d ff ff       	call   4550 <__asan_report_load4@plt>
        struct Data *them = data->mailboxes[n].higher;
    e7c0:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    e7c5:	e8 16 5d ff ff       	call   44e0 <__asan_report_load8@plt>
        for (; them->messages_count < min;) {
    e7ca:	4c 89 ff             	mov    %r15,%rdi
    e7cd:	e8 0e 5d ff ff       	call   44e0 <__asan_report_load8@plt>
        int min = them->messages_limit;
    e7d2:	e8 09 5d ff ff       	call   44e0 <__asan_report_load8@plt>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    e7d7:	e8 74 5d ff ff       	call   4550 <__asan_report_load4@plt>
  if (data->sending == 1) {
    e7dc:	e8 6f 5d ff ff       	call   4550 <__asan_report_load4@plt>
    e7e1:	e8 ea 5e ff ff       	call   46d0 <__asan_report_store8@plt>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    e7e6:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    e7eb:	e8 f0 5c ff ff       	call   44e0 <__asan_report_load8@plt>
        int min = them->messages_limit;
    e7f0:	e8 eb 5c ff ff       	call   44e0 <__asan_report_load8@plt>
        for (; them->messages_count < min;) {
    e7f5:	4c 89 ff             	mov    %r15,%rdi
    e7f8:	e8 e3 5c ff ff       	call   44e0 <__asan_report_load8@plt>
          data->n++;
    e7fd:	e8 de 5c ff ff       	call   44e0 <__asan_report_load8@plt>
          data->mailboxes[n].sent++;
    e802:	e8 d9 5c ff ff       	call   44e0 <__asan_report_load8@plt>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    e807:	4c 89 e7             	mov    %r12,%rdi
    e80a:	e8 41 5d ff ff       	call   4550 <__asan_report_load4@plt>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    e80f:	e8 3c 5d ff ff       	call   4550 <__asan_report_load4@plt>
          them->messages[them->messages_count++] = data->message; 
    e814:	48 89 ef             	mov    %rbp,%rdi
    e817:	e8 c4 5c ff ff       	call   44e0 <__asan_report_load8@plt>
    e81c:	4c 89 ff             	mov    %r15,%rdi
    e81f:	e8 ac 5e ff ff       	call   46d0 <__asan_report_store8@plt>
        int min = them->messages_limit;
    e824:	48 89 c7             	mov    %rax,%rdi
    e827:	e8 b4 5c ff ff       	call   44e0 <__asan_report_load8@plt>
        for (; them->messages_count < min;) {
    e82c:	4c 89 ff             	mov    %r15,%rdi
    e82f:	e8 ac 5c ff ff       	call   44e0 <__asan_report_load8@plt>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    e834:	e8 17 5d ff ff       	call   4550 <__asan_report_load4@plt>
    e839:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

000000000000e840 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    e840:	f3 0f 1e fa          	endbr64
    e844:	41 57                	push   %r15
  if (data->thread_index == data->task_index) {
    e846:	48 8d 8f 30 01 00 00 	lea    0x130(%rdi),%rcx
int barriered_work(struct BarrierTask *data) {
    e84d:	41 56                	push   %r14
  if (data->thread_index == data->task_index) {
    e84f:	48 89 c8             	mov    %rcx,%rax
int barriered_work(struct BarrierTask *data) {
    e852:	41 55                	push   %r13
  if (data->thread_index == data->task_index) {
    e854:	48 c1 e8 03          	shr    $0x3,%rax
int barriered_work(struct BarrierTask *data) {
    e858:	41 54                	push   %r12
    e85a:	55                   	push   %rbp
    e85b:	53                   	push   %rbx
    e85c:	48 89 fb             	mov    %rdi,%rbx
    e85f:	48 83 ec 48          	sub    $0x48,%rsp
  if (data->thread_index == data->task_index) {
    e863:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e86a:	84 c0                	test   %al,%al
    e86c:	74 08                	je     e876 <barriered_work+0x36>
    e86e:	3c 03                	cmp    $0x3,%al
    e870:	0f 8e 38 08 00 00    	jle    f0ae <barriered_work+0x86e>
    e876:	4c 8d 7b 04          	lea    0x4(%rbx),%r15
    e87a:	8b b3 30 01 00 00    	mov    0x130(%rbx),%esi
    e880:	4c 89 f8             	mov    %r15,%rax
    e883:	48 c1 e8 03          	shr    $0x3,%rax
    e887:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    e88e:	4c 89 f8             	mov    %r15,%rax
    e891:	83 e0 07             	and    $0x7,%eax
    e894:	83 c0 03             	add    $0x3,%eax
    e897:	38 d0                	cmp    %dl,%al
    e899:	7c 08                	jl     e8a3 <barriered_work+0x63>
    e89b:	84 d2                	test   %dl,%dl
    e89d:	0f 85 a3 07 00 00    	jne    f046 <barriered_work+0x806>
    e8a3:	3b 73 04             	cmp    0x4(%rbx),%esi
    e8a6:	0f 84 b4 00 00 00    	je     e960 <barriered_work+0x120>
    receive(data);
    e8ac:	48 89 df             	mov    %rbx,%rdi
    e8af:	e8 2c f6 ff ff       	call   dee0 <receive>
    while (data->scheduled == 1) {
    e8b4:	48 8d bb 4c 01 00 00 	lea    0x14c(%rbx),%rdi
    e8bb:	48 89 f8             	mov    %rdi,%rax
    e8be:	48 c1 e8 03          	shr    $0x3,%rax
    e8c2:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    e8c9:	48 89 f8             	mov    %rdi,%rax
    e8cc:	83 e0 07             	and    $0x7,%eax
    e8cf:	83 c0 03             	add    $0x3,%eax
    e8d2:	38 d0                	cmp    %dl,%al
    e8d4:	7c 08                	jl     e8de <barriered_work+0x9e>
    e8d6:	84 d2                	test   %dl,%dl
    e8d8:	0f 85 d8 07 00 00    	jne    f0b6 <barriered_work+0x876>
    e8de:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    e8e5:	4c 8d 8b 08 01 00 00 	lea    0x108(%rbx),%r9
    e8ec:	75 4e                	jne    e93c <barriered_work+0xfc>
    e8ee:	48 89 fa             	mov    %rdi,%rdx
      data->n++;
    e8f1:	4c 89 ce             	mov    %r9,%rsi
    while (data->scheduled == 1) {
    e8f4:	48 89 f9             	mov    %rdi,%rcx
      data->n++;
    e8f7:	48 c1 ee 03          	shr    $0x3,%rsi
    while (data->scheduled == 1) {
    e8fb:	83 e2 07             	and    $0x7,%edx
    e8fe:	48 c1 e9 03          	shr    $0x3,%rcx
    e902:	83 c2 03             	add    $0x3,%edx
    e905:	0f 1f 00             	nopl   (%rax)
      data->n++;
    e908:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    e90f:	0f 85 f1 06 00 00    	jne    f006 <barriered_work+0x7c6>
    e915:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    e91d:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    e920:	0f b6 81 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%eax
    e927:	38 c2                	cmp    %al,%dl
    e929:	7c 08                	jl     e933 <barriered_work+0xf3>
    e92b:	84 c0                	test   %al,%al
    e92d:	0f 85 ce 06 00 00    	jne    f001 <barriered_work+0x7c1>
    e933:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    e93a:	74 cc                	je     e908 <barriered_work+0xc8>
    sendm(data);
    e93c:	48 89 df             	mov    %rbx,%rdi
    e93f:	e8 fc f9 ff ff       	call   e340 <sendm>
  asm volatile ("sfence" ::: "memory");
    e944:	0f ae f8             	sfence
}
    e947:	48 83 c4 48          	add    $0x48,%rsp
    e94b:	31 c0                	xor    %eax,%eax
    e94d:	5b                   	pop    %rbx
    e94e:	5d                   	pop    %rbp
    e94f:	41 5c                	pop    %r12
    e951:	41 5d                	pop    %r13
    e953:	41 5e                	pop    %r14
    e955:	41 5f                	pop    %r15
    e957:	c3                   	ret
    e958:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      receive(data);
    e960:	48 89 df             	mov    %rbx,%rdi
    e963:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    e968:	e8 73 f5 ff ff       	call   dee0 <receive>
        int t = data->task_index;
    e96d:	4c 89 f8             	mov    %r15,%rax
    e970:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    e975:	48 c1 e8 03          	shr    $0x3,%rax
    e979:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    e980:	4c 89 f8             	mov    %r15,%rax
    e983:	83 e0 07             	and    $0x7,%eax
    e986:	83 c0 03             	add    $0x3,%eax
    e989:	38 d0                	cmp    %dl,%al
    e98b:	7c 08                	jl     e995 <barriered_work+0x155>
    e98d:	84 d2                	test   %dl,%dl
    e98f:	0f 85 b9 06 00 00    	jne    f04e <barriered_work+0x80e>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    e995:	48 8d 93 40 01 00 00 	lea    0x140(%rbx),%rdx
        int t = data->task_index;
    e99c:	8b 7b 04             	mov    0x4(%rbx),%edi
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    e99f:	48 89 d0             	mov    %rdx,%rax
    e9a2:	48 c1 e8 03          	shr    $0x3,%rax
    e9a6:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e9ad:	84 c0                	test   %al,%al
    e9af:	74 08                	je     e9b9 <barriered_work+0x179>
    e9b1:	3c 03                	cmp    $0x3,%al
    e9b3:	0f 8e 9d 06 00 00    	jle    f056 <barriered_work+0x816>
    e9b9:	48 63 b3 40 01 00 00 	movslq 0x140(%rbx),%rsi
    e9c0:	85 f6                	test   %esi,%esi
    e9c2:	0f 8e ec 01 00 00    	jle    ebb4 <barriered_work+0x374>
              int next_task = abs((t + 1) % (data->thread_count));
    e9c8:	4c 8d 83 34 01 00 00 	lea    0x134(%rbx),%r8
    e9cf:	8d 47 01             	lea    0x1(%rdi),%eax
    e9d2:	4c 89 c2             	mov    %r8,%rdx
    e9d5:	48 c1 ea 03          	shr    $0x3,%rdx
    e9d9:	44 0f b6 8a 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%r9d
    e9e1:	4c 89 c2             	mov    %r8,%rdx
    e9e4:	83 e2 07             	and    $0x7,%edx
    e9e7:	83 c2 03             	add    $0x3,%edx
    e9ea:	44 38 ca             	cmp    %r9b,%dl
    e9ed:	7c 09                	jl     e9f8 <barriered_work+0x1b8>
    e9ef:	45 84 c9             	test   %r9b,%r9b
    e9f2:	0f 85 28 06 00 00    	jne    f020 <barriered_work+0x7e0>
    e9f8:	99                   	cltd
    e9f9:	f7 bb 34 01 00 00    	idivl  0x134(%rbx)
    e9ff:	89 d0                	mov    %edx,%eax
    ea01:	f7 d8                	neg    %eax
    ea03:	0f 48 c2             	cmovs  %edx,%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    ea06:	48 8d 93 28 01 00 00 	lea    0x128(%rbx),%rdx
    ea0d:	49 89 d0             	mov    %rdx,%r8
    ea10:	49 c1 e8 03          	shr    $0x3,%r8
    ea14:	41 80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r8)
    ea1c:	0f 85 84 06 00 00    	jne    f0a6 <barriered_work+0x866>
    ea22:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    ea29:	4c 8d 42 20          	lea    0x20(%rdx),%r8
    ea2d:	4d 89 c1             	mov    %r8,%r9
    ea30:	49 c1 e9 03          	shr    $0x3,%r9
    ea34:	41 80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r9)
    ea3c:	0f 85 5c 06 00 00    	jne    f09e <barriered_work+0x85e>
    ea42:	48 8b 52 20          	mov    0x20(%rdx),%rdx
                data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    ea46:	4c 63 d0             	movslq %eax,%r10
    ea49:	48 8d 04 76          	lea    (%rsi,%rsi,2),%rax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    ea4d:	48 63 ef             	movslq %edi,%rbp
    ea50:	48 c1 e0 06          	shl    $0x6,%rax
    ea54:	48 c1 e5 09          	shl    $0x9,%rbp
                data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    ea58:	45 31 c9             	xor    %r9d,%r9d
    ea5b:	4c 8d 62 38          	lea    0x38(%rdx),%r12
    ea5f:	49 c1 e2 09          	shl    $0x9,%r10
    ea63:	4c 8d 44 02 38       	lea    0x38(%rdx,%rax,1),%r8
    ea68:	4d 89 e3             	mov    %r12,%r11
    ea6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    ea70:	4c 89 d8             	mov    %r11,%rax
    ea73:	48 c1 e8 03          	shr    $0x3,%rax
    ea77:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ea7e:	0f 85 8a 05 00 00    	jne    f00e <barriered_work+0x7ce>
    ea84:	49 8b 03             	mov    (%r11),%rax
    ea87:	48 01 e8             	add    %rbp,%rax
    ea8a:	48 8d b8 70 01 00 00 	lea    0x170(%rax),%rdi
    ea91:	48 89 fa             	mov    %rdi,%rdx
    ea94:	48 c1 ea 03          	shr    $0x3,%rdx
    ea98:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    ea9f:	0f 85 1c 05 00 00    	jne    efc1 <barriered_work+0x781>
    eaa5:	48 8b b8 70 01 00 00 	mov    0x170(%rax),%rdi
    eaac:	4c 89 e0             	mov    %r12,%rax
    eaaf:	48 83 c7 20          	add    $0x20,%rdi
    eab3:	eb 41                	jmp    eaf6 <barriered_work+0x2b6>
    eab5:	0f 1f 00             	nopl   (%rax)
               if (((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available == 1) {
    eab8:	4c 8d 6a 18          	lea    0x18(%rdx),%r13
    eabc:	4c 89 ee             	mov    %r13,%rsi
    eabf:	48 c1 ee 03          	shr    $0x3,%rsi
    eac3:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    eaca:	40 84 f6             	test   %sil,%sil
    eacd:	74 0a                	je     ead9 <barriered_work+0x299>
    eacf:	40 80 fe 03          	cmp    $0x3,%sil
    ead3:	0f 8e b8 04 00 00    	jle    ef91 <barriered_work+0x751>
    ead9:	83 7a 18 01          	cmpl   $0x1,0x18(%rdx)
    eadd:	0f 84 45 04 00 00    	je     ef28 <barriered_work+0x6e8>
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    eae3:	48 05 c0 00 00 00    	add    $0xc0,%rax
    eae9:	48 83 c7 28          	add    $0x28,%rdi
    eaed:	4c 39 c0             	cmp    %r8,%rax
    eaf0:	0f 84 aa 00 00 00    	je     eba0 <barriered_work+0x360>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    eaf6:	48 89 fa             	mov    %rdi,%rdx
    eaf9:	48 c1 ea 03          	shr    $0x3,%rdx
    eafd:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    eb04:	84 d2                	test   %dl,%dl
    eb06:	74 09                	je     eb11 <barriered_work+0x2d1>
    eb08:	80 fa 03             	cmp    $0x3,%dl
    eb0b:	0f 8e 7b 04 00 00    	jle    ef8c <barriered_work+0x74c>
                tmp = data->thread->all_threads[y].tasks[t].mailboxes[b].higher; 
    eb11:	48 8d 57 e8          	lea    -0x18(%rdi),%rdx
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    eb15:	8b 37                	mov    (%rdi),%esi
                tmp = data->thread->all_threads[y].tasks[t].mailboxes[b].higher; 
    eb17:	49 89 d5             	mov    %rdx,%r13
    eb1a:	49 c1 ed 03          	shr    $0x3,%r13
    eb1e:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    eb26:	0f 85 58 04 00 00    	jne    ef84 <barriered_work+0x744>
    eb2c:	48 8b 57 e8          	mov    -0x18(%rdi),%rdx
              if (kind == MAILBOX_FRIEND) {
    eb30:	83 fe 01             	cmp    $0x1,%esi
    eb33:	75 83                	jne    eab8 <barriered_work+0x278>
                data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    eb35:	48 89 c6             	mov    %rax,%rsi
    eb38:	48 c1 ee 03          	shr    $0x3,%rsi
    eb3c:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    eb43:	0f 85 60 04 00 00    	jne    efa9 <barriered_work+0x769>
    eb49:	48 8b 30             	mov    (%rax),%rsi
    eb4c:	4c 01 d6             	add    %r10,%rsi
    eb4f:	4c 8d ae 70 01 00 00 	lea    0x170(%rsi),%r13
    eb56:	4d 89 ee             	mov    %r13,%r14
    eb59:	49 c1 ee 03          	shr    $0x3,%r14
    eb5d:	41 80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r14)
    eb65:	0f 85 2e 04 00 00    	jne    ef99 <barriered_work+0x759>
    eb6b:	4c 8b b6 70 01 00 00 	mov    0x170(%rsi),%r14
    eb72:	4d 01 ce             	add    %r9,%r14
    eb75:	4d 89 f5             	mov    %r14,%r13
    eb78:	49 c1 ed 03          	shr    $0x3,%r13
    eb7c:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    eb84:	0f 85 17 04 00 00    	jne    efa1 <barriered_work+0x761>
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    eb8a:	48 05 c0 00 00 00    	add    $0xc0,%rax
                data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    eb90:	49 89 16             	mov    %rdx,(%r14)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    eb93:	48 83 c7 28          	add    $0x28,%rdi
    eb97:	4c 39 c0             	cmp    %r8,%rax
    eb9a:	0f 85 56 ff ff ff    	jne    eaf6 <barriered_work+0x2b6>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    eba0:	49 81 c3 c0 00 00 00 	add    $0xc0,%r11
    eba7:	49 83 c1 28          	add    $0x28,%r9
    ebab:	4d 39 c3             	cmp    %r8,%r11
    ebae:	0f 85 bc fe ff ff    	jne    ea70 <barriered_work+0x230>
      asm volatile ("sfence" ::: "memory");
    ebb4:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    ebb7:	48 8d 83 50 01 00 00 	lea    0x150(%rbx),%rax
    ebbe:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    ebc3:	48 c1 e8 03          	shr    $0x3,%rax
    ebc7:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ebce:	0f 85 59 04 00 00    	jne    f02d <barriered_work+0x7ed>
    ebd4:	48 8d 83 60 01 00 00 	lea    0x160(%rbx),%rax
    ebdb:	48 8b b3 50 01 00 00 	mov    0x150(%rbx),%rsi
    ebe2:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    ebe7:	48 c1 e8 03          	shr    $0x3,%rax
    ebeb:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ebf2:	0f 85 3f 04 00 00    	jne    f037 <barriered_work+0x7f7>
    ebf8:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    ebff:	31 ff                	xor    %edi,%edi
    ec01:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    int modcount = ++data->thread->protected_state->modcount;
    ec06:	4c 8d b3 28 01 00 00 	lea    0x128(%rbx),%r14
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    ec0d:	48 c1 e0 05          	shl    $0x5,%rax
    ec11:	48 01 c6             	add    %rax,%rsi
    ec14:	e8 67 58 ff ff       	call   4480 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    ec19:	4c 89 f0             	mov    %r14,%rax
    ec1c:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    ec21:	48 c1 e8 03          	shr    $0x3,%rax
    ec25:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ec2c:	0f 85 89 04 00 00    	jne    f0bb <barriered_work+0x87b>
    ec32:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    ec39:	48 8d 78 48          	lea    0x48(%rax),%rdi
    ec3d:	48 89 fe             	mov    %rdi,%rsi
    ec40:	48 c1 ee 03          	shr    $0x3,%rsi
    ec44:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    ec4b:	0f 85 72 04 00 00    	jne    f0c3 <barriered_work+0x883>
    ec51:	48 8b 50 48          	mov    0x48(%rax),%rdx
    ec55:	48 8d 7a 10          	lea    0x10(%rdx),%rdi
    ec59:	48 89 fe             	mov    %rdi,%rsi
    ec5c:	48 c1 ee 03          	shr    $0x3,%rsi
    ec60:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    ec67:	40 84 f6             	test   %sil,%sil
    ec6a:	74 0a                	je     ec76 <barriered_work+0x436>
    ec6c:	40 80 fe 03          	cmp    $0x3,%sil
    ec70:	0f 8e e8 03 00 00    	jle    f05e <barriered_work+0x81e>
    ec76:	8b 7a 10             	mov    0x10(%rdx),%edi
    while (data->scheduled == 1) {
    ec79:	48 8d ab 4c 01 00 00 	lea    0x14c(%rbx),%rbp
    int modcount = ++data->thread->protected_state->modcount;
    ec80:	44 8d 57 01          	lea    0x1(%rdi),%r10d
    ec84:	44 89 52 10          	mov    %r10d,0x10(%rdx)
    while (data->scheduled == 1) {
    ec88:	48 89 ea             	mov    %rbp,%rdx
    ec8b:	48 c1 ea 03          	shr    $0x3,%rdx
    ec8f:	44 0f b6 82 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%r8d
    ec97:	48 89 ea             	mov    %rbp,%rdx
    ec9a:	83 e2 07             	and    $0x7,%edx
    ec9d:	83 c2 03             	add    $0x3,%edx
    eca0:	44 38 c2             	cmp    %r8b,%dl
    eca3:	7c 09                	jl     ecae <barriered_work+0x46e>
    eca5:	45 84 c0             	test   %r8b,%r8b
    eca8:	0f 85 b5 03 00 00    	jne    f063 <barriered_work+0x823>
    ecae:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    ecb5:	4c 8d 8b 08 01 00 00 	lea    0x108(%rbx),%r9
    ecbc:	0f 85 c9 01 00 00    	jne    ee8b <barriered_work+0x64b>
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    ecc2:	4c 8d 9b 20 01 00 00 	lea    0x120(%rbx),%r11
    ecc9:	48 89 cf             	mov    %rcx,%rdi
      data->n++;
    eccc:	4d 89 cd             	mov    %r9,%r13
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    eccf:	44 89 54 24 24       	mov    %r10d,0x24(%rsp)
    ecd4:	48 c1 ef 03          	shr    $0x3,%rdi
    ecd8:	4d 89 dc             	mov    %r11,%r12
    ecdb:	48 89 4c 24 28       	mov    %rcx,0x28(%rsp)
      data->n++;
    ece0:	49 c1 ed 03          	shr    $0x3,%r13
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    ece4:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    ece9:	49 c1 ec 03          	shr    $0x3,%r12
    eced:	4c 89 4c 24 30       	mov    %r9,0x30(%rsp)
    ecf2:	4c 89 5c 24 38       	mov    %r11,0x38(%rsp)
    ecf7:	eb 22                	jmp    ed1b <barriered_work+0x4db>
    ecf9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    if (modcount != data->thread->protected_state->modcount) {
    ed00:	4c 89 f0             	mov    %r14,%rax
    ed03:	48 c1 e8 03          	shr    $0x3,%rax
    ed07:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ed0e:	0f 85 57 03 00 00    	jne    f06b <barriered_work+0x82b>
    ed14:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
      data->n++;
    ed1b:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    ed23:	0f 85 ed 02 00 00    	jne    f016 <barriered_work+0x7d6>
    ed29:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    ed31:	41 80 bc 24 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r12)
    ed3a:	0f 85 86 02 00 00    	jne    efc6 <barriered_work+0x786>
    ed40:	48 8d 78 18          	lea    0x18(%rax),%rdi
    ed44:	48 8b 8b 20 01 00 00 	mov    0x120(%rbx),%rcx
    ed4b:	48 89 fe             	mov    %rdi,%rsi
    ed4e:	48 c1 ee 03          	shr    $0x3,%rsi
    ed52:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    ed59:	0f 85 71 02 00 00    	jne    efd0 <barriered_work+0x790>
    ed5f:	48 8b 70 18          	mov    0x18(%rax),%rsi
    ed63:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    ed68:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    ed6f:	84 c0                	test   %al,%al
    ed71:	74 08                	je     ed7b <barriered_work+0x53b>
    ed73:	3c 03                	cmp    $0x3,%al
    ed75:	0f 8e 5a 02 00 00    	jle    efd5 <barriered_work+0x795>
    ed7b:	48 63 83 30 01 00 00 	movslq 0x130(%rbx),%rax
    ed82:	48 8d 3c c6          	lea    (%rsi,%rax,8),%rdi
    ed86:	48 89 f8             	mov    %rdi,%rax
    ed89:	48 c1 e8 03          	shr    $0x3,%rax
    ed8d:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ed94:	0f 85 45 02 00 00    	jne    efdf <barriered_work+0x79f>
    ed9a:	48 8b 07             	mov    (%rdi),%rax
    ed9d:	48 8d 78 38          	lea    0x38(%rax),%rdi
    eda1:	48 89 fe             	mov    %rdi,%rsi
    eda4:	48 c1 ee 03          	shr    $0x3,%rsi
    eda8:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    edaf:	0f 85 2f 02 00 00    	jne    efe4 <barriered_work+0x7a4>
    edb5:	48 8b 78 38          	mov    0x38(%rax),%rdi
    edb9:	4c 89 f8             	mov    %r15,%rax
    edbc:	48 c1 e8 03          	shr    $0x3,%rax
    edc0:	0f b6 b0 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%esi
    edc7:	4c 89 f8             	mov    %r15,%rax
    edca:	83 e0 07             	and    $0x7,%eax
    edcd:	83 c0 03             	add    $0x3,%eax
    edd0:	40 38 f0             	cmp    %sil,%al
    edd3:	7c 09                	jl     edde <barriered_work+0x59e>
    edd5:	40 84 f6             	test   %sil,%sil
    edd8:	0f 85 0b 02 00 00    	jne    efe9 <barriered_work+0x7a9>
    edde:	48 63 43 04          	movslq 0x4(%rbx),%rax
    ede2:	48 c1 e0 09          	shl    $0x9,%rax
    ede6:	48 01 c7             	add    %rax,%rdi
    ede9:	ff d1                	call   *%rcx
      asm volatile ("sfence" ::: "memory");
    edeb:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    edee:	48 89 e8             	mov    %rbp,%rax
    edf1:	48 c1 e8 03          	shr    $0x3,%rax
    edf5:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    edfc:	48 89 e8             	mov    %rbp,%rax
    edff:	83 e0 07             	and    $0x7,%eax
    ee02:	83 c0 03             	add    $0x3,%eax
    ee05:	38 c8                	cmp    %cl,%al
    ee07:	7c 08                	jl     ee11 <barriered_work+0x5d1>
    ee09:	84 c9                	test   %cl,%cl
    ee0b:	0f 85 e0 01 00 00    	jne    eff1 <barriered_work+0x7b1>
    ee11:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    ee18:	0f 84 e2 fe ff ff    	je     ed00 <barriered_work+0x4c0>
    if (modcount != data->thread->protected_state->modcount) {
    ee1e:	4c 89 f0             	mov    %r14,%rax
    ee21:	44 8b 54 24 24       	mov    0x24(%rsp),%r10d
    ee26:	48 c1 e8 03          	shr    $0x3,%rax
    ee2a:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ee31:	0f 85 3c 02 00 00    	jne    f073 <barriered_work+0x833>
    ee37:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    ee3e:	48 8d 78 48          	lea    0x48(%rax),%rdi
    ee42:	48 89 fa             	mov    %rdi,%rdx
    ee45:	48 c1 ea 03          	shr    $0x3,%rdx
    ee49:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    ee50:	0f 85 25 02 00 00    	jne    f07b <barriered_work+0x83b>
    ee56:	48 8b 40 48          	mov    0x48(%rax),%rax
    ee5a:	48 8d 78 10          	lea    0x10(%rax),%rdi
    ee5e:	48 89 fa             	mov    %rdi,%rdx
    ee61:	48 c1 ea 03          	shr    $0x3,%rdx
    ee65:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    ee6c:	84 d2                	test   %dl,%dl
    ee6e:	74 09                	je     ee79 <barriered_work+0x639>
    ee70:	80 fa 03             	cmp    $0x3,%dl
    ee73:	0f 8e af 01 00 00    	jle    f028 <barriered_work+0x7e8>
    ee79:	44 3b 50 10          	cmp    0x10(%rax),%r10d
    ee7d:	74 0c                	je     ee8b <barriered_work+0x64b>
    ee7f:	48 8d 3d 9a 20 00 00 	lea    0x209a(%rip),%rdi        # 10f20 <_IO_stdin_used+0xf20>
    ee86:	e8 75 59 ff ff       	call   4800 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    ee8b:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    ee90:	48 c1 e8 03          	shr    $0x3,%rax
    ee94:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ee9b:	0f 85 df 01 00 00    	jne    f080 <barriered_work+0x840>
    eea1:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    eea6:	48 8b 93 50 01 00 00 	mov    0x150(%rbx),%rdx
    eead:	48 c1 ed 03          	shr    $0x3,%rbp
    eeb1:	80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rbp)
    eeb8:	0f 85 cc 01 00 00    	jne    f08a <barriered_work+0x84a>
    eebe:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    eec5:	31 ff                	xor    %edi,%edi
    eec7:	48 c1 e0 05          	shl    $0x5,%rax
    eecb:	48 8d 74 02 10       	lea    0x10(%rdx,%rax,1),%rsi
    eed0:	e8 ab 55 ff ff       	call   4480 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    eed5:	80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rbp)
    eedc:	0f 85 b2 01 00 00    	jne    f094 <barriered_work+0x854>
    eee2:	48 8d bb 58 01 00 00 	lea    0x158(%rbx),%rdi
    eee9:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    eef0:	48 89 fa             	mov    %rdi,%rdx
    eef3:	48 c1 ea 03          	shr    $0x3,%rdx
    eef7:	48 83 c0 01          	add    $0x1,%rax
    eefb:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    ef02:	0f 85 39 01 00 00    	jne    f041 <barriered_work+0x801>
    ef08:	48 99                	cqto
    sendm(data);
    ef0a:	48 89 df             	mov    %rbx,%rdi
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    ef0d:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    ef14:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    sendm(data);
    ef1b:	e8 20 f4 ff ff       	call   e340 <sendm>
    ef20:	e9 1f fa ff ff       	jmp    e944 <barriered_work+0x104>
    ef25:	0f 1f 00             	nopl   (%rax)
                data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    ef28:	48 89 c6             	mov    %rax,%rsi
    ef2b:	48 c1 ee 03          	shr    $0x3,%rsi
    ef2f:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    ef36:	75 79                	jne    efb1 <barriered_work+0x771>
    ef38:	48 8b 30             	mov    (%rax),%rsi
    ef3b:	4c 01 d6             	add    %r10,%rsi
    ef3e:	4c 8d ae 70 01 00 00 	lea    0x170(%rsi),%r13
    ef45:	4d 89 ee             	mov    %r13,%r14
    ef48:	49 c1 ee 03          	shr    $0x3,%r14
    ef4c:	41 80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r14)
    ef54:	0f 85 9f 00 00 00    	jne    eff9 <barriered_work+0x7b9>
    ef5a:	4c 8b b6 70 01 00 00 	mov    0x170(%rsi),%r14
    ef61:	4d 01 ce             	add    %r9,%r14
    ef64:	4d 89 f5             	mov    %r14,%r13
    ef67:	49 c1 ed 03          	shr    $0x3,%r13
    ef6b:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    ef73:	75 44                	jne    efb9 <barriered_work+0x779>
    ef75:	49 89 16             	mov    %rdx,(%r14)
                ((struct Data*)data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower)->available = 0;
    ef78:	c7 42 18 00 00 00 00 	movl   $0x0,0x18(%rdx)
    ef7f:	e9 5f fb ff ff       	jmp    eae3 <barriered_work+0x2a3>
                tmp = data->thread->all_threads[y].tasks[t].mailboxes[b].higher; 
    ef84:	48 89 d7             	mov    %rdx,%rdi
    ef87:	e8 54 55 ff ff       	call   44e0 <__asan_report_load8@plt>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    ef8c:	e8 bf 55 ff ff       	call   4550 <__asan_report_load4@plt>
               if (((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available == 1) {
    ef91:	4c 89 ef             	mov    %r13,%rdi
    ef94:	e8 b7 55 ff ff       	call   4550 <__asan_report_load4@plt>
                data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    ef99:	4c 89 ef             	mov    %r13,%rdi
    ef9c:	e8 3f 55 ff ff       	call   44e0 <__asan_report_load8@plt>
    efa1:	4c 89 f7             	mov    %r14,%rdi
    efa4:	e8 27 57 ff ff       	call   46d0 <__asan_report_store8@plt>
    efa9:	48 89 c7             	mov    %rax,%rdi
    efac:	e8 2f 55 ff ff       	call   44e0 <__asan_report_load8@plt>
                data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    efb1:	48 89 c7             	mov    %rax,%rdi
    efb4:	e8 27 55 ff ff       	call   44e0 <__asan_report_load8@plt>
    efb9:	4c 89 f7             	mov    %r14,%rdi
    efbc:	e8 0f 57 ff ff       	call   46d0 <__asan_report_store8@plt>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    efc1:	e8 1a 55 ff ff       	call   44e0 <__asan_report_load8@plt>
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    efc6:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    efcb:	e8 10 55 ff ff       	call   44e0 <__asan_report_load8@plt>
    efd0:	e8 0b 55 ff ff       	call   44e0 <__asan_report_load8@plt>
    efd5:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    efda:	e8 71 55 ff ff       	call   4550 <__asan_report_load4@plt>
    efdf:	e8 fc 54 ff ff       	call   44e0 <__asan_report_load8@plt>
    efe4:	e8 f7 54 ff ff       	call   44e0 <__asan_report_load8@plt>
    efe9:	4c 89 ff             	mov    %r15,%rdi
    efec:	e8 5f 55 ff ff       	call   4550 <__asan_report_load4@plt>
    while (data->scheduled == 1) {
    eff1:	48 89 ef             	mov    %rbp,%rdi
    eff4:	e8 57 55 ff ff       	call   4550 <__asan_report_load4@plt>
                data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    eff9:	4c 89 ef             	mov    %r13,%rdi
    effc:	e8 df 54 ff ff       	call   44e0 <__asan_report_load8@plt>
    while (data->scheduled == 1) {
    f001:	e8 4a 55 ff ff       	call   4550 <__asan_report_load4@plt>
      data->n++;
    f006:	4c 89 cf             	mov    %r9,%rdi
    f009:	e8 d2 54 ff ff       	call   44e0 <__asan_report_load8@plt>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    f00e:	4c 89 df             	mov    %r11,%rdi
    f011:	e8 ca 54 ff ff       	call   44e0 <__asan_report_load8@plt>
      data->n++;
    f016:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    f01b:	e8 c0 54 ff ff       	call   44e0 <__asan_report_load8@plt>
              int next_task = abs((t + 1) % (data->thread_count));
    f020:	4c 89 c7             	mov    %r8,%rdi
    f023:	e8 28 55 ff ff       	call   4550 <__asan_report_load4@plt>
    if (modcount != data->thread->protected_state->modcount) {
    f028:	e8 23 55 ff ff       	call   4550 <__asan_report_load4@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    f02d:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    f032:	e8 a9 54 ff ff       	call   44e0 <__asan_report_load8@plt>
    f037:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    f03c:	e8 9f 54 ff ff       	call   44e0 <__asan_report_load8@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    f041:	e8 9a 54 ff ff       	call   44e0 <__asan_report_load8@plt>
  if (data->thread_index == data->task_index) {
    f046:	4c 89 ff             	mov    %r15,%rdi
    f049:	e8 02 55 ff ff       	call   4550 <__asan_report_load4@plt>
        int t = data->task_index;
    f04e:	4c 89 ff             	mov    %r15,%rdi
    f051:	e8 fa 54 ff ff       	call   4550 <__asan_report_load4@plt>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    f056:	48 89 d7             	mov    %rdx,%rdi
    f059:	e8 f2 54 ff ff       	call   4550 <__asan_report_load4@plt>
    int modcount = ++data->thread->protected_state->modcount;
    f05e:	e8 ed 54 ff ff       	call   4550 <__asan_report_load4@plt>
    while (data->scheduled == 1) {
    f063:	48 89 ef             	mov    %rbp,%rdi
    f066:	e8 e5 54 ff ff       	call   4550 <__asan_report_load4@plt>
    if (modcount != data->thread->protected_state->modcount) {
    f06b:	4c 89 f7             	mov    %r14,%rdi
    f06e:	e8 6d 54 ff ff       	call   44e0 <__asan_report_load8@plt>
    f073:	4c 89 f7             	mov    %r14,%rdi
    f076:	e8 65 54 ff ff       	call   44e0 <__asan_report_load8@plt>
    f07b:	e8 60 54 ff ff       	call   44e0 <__asan_report_load8@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    f080:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    f085:	e8 56 54 ff ff       	call   44e0 <__asan_report_load8@plt>
    f08a:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    f08f:	e8 4c 54 ff ff       	call   44e0 <__asan_report_load8@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    f094:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    f099:	e8 42 54 ff ff       	call   44e0 <__asan_report_load8@plt>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    f09e:	4c 89 c7             	mov    %r8,%rdi
    f0a1:	e8 3a 54 ff ff       	call   44e0 <__asan_report_load8@plt>
    f0a6:	48 89 d7             	mov    %rdx,%rdi
    f0a9:	e8 32 54 ff ff       	call   44e0 <__asan_report_load8@plt>
  if (data->thread_index == data->task_index) {
    f0ae:	48 89 cf             	mov    %rcx,%rdi
    f0b1:	e8 9a 54 ff ff       	call   4550 <__asan_report_load4@plt>
    while (data->scheduled == 1) {
    f0b6:	e8 95 54 ff ff       	call   4550 <__asan_report_load4@plt>
    int modcount = ++data->thread->protected_state->modcount;
    f0bb:	4c 89 f7             	mov    %r14,%rdi
    f0be:	e8 1d 54 ff ff       	call   44e0 <__asan_report_load8@plt>
    f0c3:	e8 18 54 ff ff       	call   44e0 <__asan_report_load8@plt>
    f0c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

000000000000f0d0 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    f0d0:	f3 0f 1e fa          	endbr64
    f0d4:	53                   	push   %rbx
    f0d5:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    f0d8:	e8 a3 df ff ff       	call   d080 <barriered_work_ingest>
  barriered_work(data);
    f0dd:	48 89 df             	mov    %rbx,%rdi
}
    f0e0:	5b                   	pop    %rbx
  barriered_work(data);
    f0e1:	e9 5a f7 ff ff       	jmp    e840 <barriered_work>
    f0e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

000000000000f0f0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    f0f0:	f3 0f 1e fa          	endbr64
}
    f0f4:	31 c0                	xor    %eax,%eax
    f0f6:	c3                   	ret
    f0f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

000000000000f100 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    f100:	f3 0f 1e fa          	endbr64
    f104:	31 c0                	xor    %eax,%eax
    f106:	c3                   	ret
    f107:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

000000000000f110 <after>:
int after(struct timespec left, struct timespec right) {
    f110:	f3 0f 1e fa          	endbr64
    f114:	41 57                	push   %r15
    f116:	49 89 cf             	mov    %rcx,%r15
    f119:	41 56                	push   %r14
    f11b:	49 89 d6             	mov    %rdx,%r14
    f11e:	41 55                	push   %r13
    f120:	55                   	push   %rbp
    f121:	48 89 fd             	mov    %rdi,%rbp
    f124:	53                   	push   %rbx
    f125:	48 81 ec 90 00 00 00 	sub    $0x90,%rsp
    f12c:	8b 05 4e 6a 00 00    	mov    0x6a4e(%rip),%eax        # 15b80 <__asan_option_detect_stack_use_after_return@@Base>
    f132:	48 8d 5c 24 10       	lea    0x10(%rsp),%rbx
    f137:	49 89 dd             	mov    %rbx,%r13
    f13a:	85 c0                	test   %eax,%eax
    f13c:	0f 85 2e 01 00 00    	jne    f270 <after+0x160>
    f142:	48 8d 05 47 2f 00 00 	lea    0x2f47(%rip),%rax        # 12090 <_IO_stdin_used+0x2090>
    f149:	48 c7 03 b3 8a b5 41 	movq   $0x41b58ab3,(%rbx)
  return left.tv_sec > right.tv_sec &&
    f150:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
int after(struct timespec left, struct timespec right) {
    f154:	48 89 43 08          	mov    %rax,0x8(%rbx)
    f158:	48 8d 05 b1 ff ff ff 	lea    -0x4f(%rip),%rax        # f110 <after>
    f15f:	48 8d 8b 80 00 00 00 	lea    0x80(%rbx),%rcx
    f166:	48 89 43 10          	mov    %rax,0x10(%rbx)
    f16a:	48 89 d8             	mov    %rbx,%rax
    f16d:	48 c1 e8 03          	shr    $0x3,%rax
    f171:	c7 80 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%rax)
    f17b:	c7 80 04 80 ff 7f 00 00 f2 f2 	movl   $0xf2f20000,0x7fff8004(%rax)
    f185:	c7 80 08 80 ff 7f 00 00 f3 f3 	movl   $0xf3f30000,0x7fff8008(%rax)
    f18f:	64 48 8b 14 25 28 00 00 00 	mov    %fs:0x28,%rdx
    f198:	48 89 94 24 88 00 00 00 	mov    %rdx,0x88(%rsp)
    f1a0:	31 d2                	xor    %edx,%edx
  return left.tv_sec > right.tv_sec &&
    f1a2:	48 89 fa             	mov    %rdi,%rdx
int after(struct timespec left, struct timespec right) {
    f1a5:	48 89 69 a0          	mov    %rbp,-0x60(%rcx)
  return left.tv_sec > right.tv_sec &&
    f1a9:	48 c1 ea 03          	shr    $0x3,%rdx
int after(struct timespec left, struct timespec right) {
    f1ad:	48 89 71 a8          	mov    %rsi,-0x58(%rcx)
  return left.tv_sec > right.tv_sec &&
    f1b1:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
int after(struct timespec left, struct timespec right) {
    f1b8:	4c 89 71 c0          	mov    %r14,-0x40(%rcx)
    f1bc:	4c 89 79 c8          	mov    %r15,-0x38(%rcx)
  return left.tv_sec > right.tv_sec &&
    f1c0:	0f 85 a5 00 00 00    	jne    f26b <after+0x15b>
    f1c6:	48 8d 7b 40          	lea    0x40(%rbx),%rdi
    f1ca:	48 89 fa             	mov    %rdi,%rdx
    f1cd:	48 c1 ea 03          	shr    $0x3,%rdx
    f1d1:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f1d8:	0f 85 88 00 00 00    	jne    f266 <after+0x156>
    f1de:	48 3b 69 c0          	cmp    -0x40(%rcx),%rbp
    f1e2:	7e 74                	jle    f258 <after+0x148>
         left.tv_nsec > right.tv_nsec;
    f1e4:	48 8d 7b 28          	lea    0x28(%rbx),%rdi
    f1e8:	48 89 fa             	mov    %rdi,%rdx
    f1eb:	48 c1 ea 03          	shr    $0x3,%rdx
    f1ef:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f1f6:	75 69                	jne    f261 <after+0x151>
    f1f8:	48 8d 7b 48          	lea    0x48(%rbx),%rdi
    f1fc:	48 89 fa             	mov    %rdi,%rdx
    f1ff:	48 c1 ea 03          	shr    $0x3,%rdx
    f203:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f20a:	75 50                	jne    f25c <after+0x14c>
  return left.tv_sec > right.tv_sec &&
    f20c:	31 d2                	xor    %edx,%edx
    f20e:	48 3b 71 c8          	cmp    -0x38(%rcx),%rsi
    f212:	0f 9f c2             	setg   %dl
int after(struct timespec left, struct timespec right) {
    f215:	49 39 dd             	cmp    %rbx,%r13
    f218:	75 76                	jne    f290 <after+0x180>
    f21a:	48 c7 80 00 80 ff 7f 00 00 00 00 	movq   $0x0,0x7fff8000(%rax)
    f225:	c7 80 08 80 ff 7f 00 00 00 00 	movl   $0x0,0x7fff8008(%rax)
}
    f22f:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    f237:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    f240:	75 7c                	jne    f2be <after+0x1ae>
    f242:	48 81 c4 90 00 00 00 	add    $0x90,%rsp
    f249:	89 d0                	mov    %edx,%eax
    f24b:	5b                   	pop    %rbx
    f24c:	5d                   	pop    %rbp
    f24d:	41 5d                	pop    %r13
    f24f:	41 5e                	pop    %r14
    f251:	41 5f                	pop    %r15
    f253:	c3                   	ret
    f254:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    f258:	31 d2                	xor    %edx,%edx
    f25a:	eb b9                	jmp    f215 <after+0x105>
         left.tv_nsec > right.tv_nsec;
    f25c:	e8 7f 52 ff ff       	call   44e0 <__asan_report_load8@plt>
    f261:	e8 7a 52 ff ff       	call   44e0 <__asan_report_load8@plt>
  return left.tv_sec > right.tv_sec &&
    f266:	e8 75 52 ff ff       	call   44e0 <__asan_report_load8@plt>
    f26b:	e8 70 52 ff ff       	call   44e0 <__asan_report_load8@plt>
int after(struct timespec left, struct timespec right) {
    f270:	bf 60 00 00 00       	mov    $0x60,%edi
    f275:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    f27a:	e8 71 52 ff ff       	call   44f0 <__asan_stack_malloc_1@plt>
    f27f:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    f284:	48 85 c0             	test   %rax,%rax
    f287:	48 0f 45 d8          	cmovne %rax,%rbx
    f28b:	e9 b2 fe ff ff       	jmp    f142 <after+0x32>
    f290:	48 b9 f5 f5 f5 f5 f5 f5 f5 f5 	movabs $0xf5f5f5f5f5f5f5f5,%rcx
    f29a:	48 c7 03 0e 36 e0 45 	movq   $0x45e0360e,(%rbx)
    f2a1:	48 89 88 00 80 ff 7f 	mov    %rcx,0x7fff8000(%rax)
    f2a8:	c7 80 08 80 ff 7f f5 f5 f5 f5 	movl   $0xf5f5f5f5,0x7fff8008(%rax)
    f2b2:	48 8b 43 78          	mov    0x78(%rbx),%rax
    f2b6:	c6 00 00             	movb   $0x0,(%rax)
    f2b9:	e9 71 ff ff ff       	jmp    f22f <after+0x11f>
}
    f2be:	e8 ed 53 ff ff       	call   46b0 <__stack_chk_fail@plt>
    f2c3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    f2ce:	66 90                	xchg   %ax,%ax

000000000000f2d0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    f2d0:	f3 0f 1e fa          	endbr64
    f2d4:	41 57                	push   %r15
    f2d6:	41 56                	push   %r14
    f2d8:	49 89 f6             	mov    %rsi,%r14
    f2db:	41 55                	push   %r13
    f2dd:	49 89 cd             	mov    %rcx,%r13
    f2e0:	41 54                	push   %r12
    f2e2:	49 89 d4             	mov    %rdx,%r12
    f2e5:	55                   	push   %rbp
    f2e6:	48 89 fd             	mov    %rdi,%rbp
    f2e9:	53                   	push   %rbx
    f2ea:	48 81 ec d8 00 00 00 	sub    $0xd8,%rsp
    f2f1:	8b 05 89 68 00 00    	mov    0x6889(%rip),%eax        # 15b80 <__asan_option_detect_stack_use_after_return@@Base>
    f2f7:	48 8d 5c 24 10       	lea    0x10(%rsp),%rbx
    f2fc:	49 89 df             	mov    %rbx,%r15
    f2ff:	85 c0                	test   %eax,%eax
    f301:	0f 85 05 02 00 00    	jne    f50c <within+0x23c>
    f307:	48 8d 35 aa 2d 00 00 	lea    0x2daa(%rip),%rsi        # 120b8 <_IO_stdin_used+0x20b8>
    f30e:	48 89 d9             	mov    %rbx,%rcx
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f311:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    f315:	48 c7 03 b3 8a b5 41 	movq   $0x41b58ab3,(%rbx)
    f31c:	48 89 73 08          	mov    %rsi,0x8(%rbx)
    f320:	48 c1 e9 03          	shr    $0x3,%rcx
    f324:	48 8d 35 a5 ff ff ff 	lea    -0x5b(%rip),%rsi        # f2d0 <within>
    f32b:	48 8d 83 c0 00 00 00 	lea    0xc0(%rbx),%rax
    f332:	48 89 73 10          	mov    %rsi,0x10(%rbx)
    f336:	f3 0f 6f 8c 24 10 01 00 00 	movdqu 0x110(%rsp),%xmm1
    f33f:	c7 81 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%rcx)
    f349:	c7 81 04 80 ff 7f 00 00 f2 f2 	movl   $0xf2f20000,0x7fff8004(%rcx)
    f353:	c7 81 08 80 ff 7f 00 00 f2 f2 	movl   $0xf2f20000,0x7fff8008(%rcx)
    f35d:	c7 81 0c 80 ff 7f 00 00 f2 f2 	movl   $0xf2f20000,0x7fff800c(%rcx)
    f367:	c7 81 10 80 ff 7f 00 00 f3 f3 	movl   $0xf3f30000,0x7fff8010(%rcx)
    f371:	64 48 8b 14 25 28 00 00 00 	mov    %fs:0x28,%rdx
    f37a:	48 89 94 24 c8 00 00 00 	mov    %rdx,0xc8(%rsp)
    f382:	31 d2                	xor    %edx,%edx
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f384:	48 89 fa             	mov    %rdi,%rdx
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    f387:	48 89 a8 60 ff ff ff 	mov    %rbp,-0xa0(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f38e:	48 c1 ea 03          	shr    $0x3,%rdx
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    f392:	4c 89 b0 68 ff ff ff 	mov    %r14,-0x98(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f399:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    f3a0:	4c 89 60 80          	mov    %r12,-0x80(%rax)
    f3a4:	4c 89 68 88          	mov    %r13,-0x78(%rax)
    f3a8:	4c 89 40 a0          	mov    %r8,-0x60(%rax)
    f3ac:	4c 89 48 a8          	mov    %r9,-0x58(%rax)
    f3b0:	0f 11 48 c0          	movups %xmm1,-0x40(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f3b4:	0f 85 4d 01 00 00    	jne    f507 <within+0x237>
    f3ba:	48 8d 7b 40          	lea    0x40(%rbx),%rdi
    f3be:	48 89 fa             	mov    %rdi,%rdx
    f3c1:	48 c1 ea 03          	shr    $0x3,%rdx
    f3c5:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f3cc:	0f 85 30 01 00 00    	jne    f502 <within+0x232>
    f3d2:	48 3b 68 80          	cmp    -0x80(%rax),%rbp
    f3d6:	0f 8f 04 01 00 00    	jg     f4e0 <within+0x210>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    f3dc:	48 8d 7b 60          	lea    0x60(%rbx),%rdi
    f3e0:	48 89 fa             	mov    %rdi,%rdx
    f3e3:	48 c1 ea 03          	shr    $0x3,%rdx
    f3e7:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f3ee:	0f 85 09 01 00 00    	jne    f4fd <within+0x22d>
    f3f4:	48 8d 7b 68          	lea    0x68(%rbx),%rdi
    f3f8:	4c 8b 50 a0          	mov    -0x60(%rax),%r10
    f3fc:	48 89 fa             	mov    %rdi,%rdx
    f3ff:	48 c1 ea 03          	shr    $0x3,%rdx
    f403:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f40a:	0f 85 e8 00 00 00    	jne    f4f8 <within+0x228>
    f410:	48 8d bb 80 00 00 00 	lea    0x80(%rbx),%rdi
    f417:	4c 8b 40 a8          	mov    -0x58(%rax),%r8
    f41b:	48 89 fa             	mov    %rdi,%rdx
    f41e:	48 c1 ea 03          	shr    $0x3,%rdx
    f422:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f429:	0f 85 c4 00 00 00    	jne    f4f3 <within+0x223>
    f42f:	48 8d bb 88 00 00 00 	lea    0x88(%rbx),%rdi
    f436:	4c 8b 48 c0          	mov    -0x40(%rax),%r9
    f43a:	48 89 fa             	mov    %rdi,%rdx
    f43d:	48 c1 ea 03          	shr    $0x3,%rdx
    f441:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f448:	0f 85 a0 00 00 00    	jne    f4ee <within+0x21e>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f44e:	48 8d 7b 28          	lea    0x28(%rbx),%rdi
    f452:	48 8b 70 c8          	mov    -0x38(%rax),%rsi
    f456:	48 89 fa             	mov    %rdi,%rdx
    f459:	48 c1 ea 03          	shr    $0x3,%rdx
    f45d:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f464:	0f 85 7f 00 00 00    	jne    f4e9 <within+0x219>
    f46a:	48 8d 7b 48          	lea    0x48(%rbx),%rdi
    f46e:	48 89 fa             	mov    %rdi,%rdx
    f471:	48 c1 ea 03          	shr    $0x3,%rdx
    f475:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f47c:	75 66                	jne    f4e4 <within+0x214>
    f47e:	4c 3b 70 88          	cmp    -0x78(%rax),%r14
    f482:	0f 9e c2             	setle  %dl
    f485:	4d 39 ca             	cmp    %r9,%r10
    f488:	0f 9e c0             	setle  %al
    f48b:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    f48d:	31 c0                	xor    %eax,%eax
    f48f:	49 39 f0             	cmp    %rsi,%r8
    f492:	0f 9e c0             	setle  %al
    f495:	21 d0                	and    %edx,%eax
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    f497:	49 39 df             	cmp    %rbx,%r15
    f49a:	0f 85 94 00 00 00    	jne    f534 <within+0x264>
    f4a0:	c7 81 10 80 ff 7f 00 00 00 00 	movl   $0x0,0x7fff8010(%rcx)
    f4aa:	66 0f ef c0          	pxor   %xmm0,%xmm0
    f4ae:	0f 11 81 00 80 ff 7f 	movups %xmm0,0x7fff8000(%rcx)
}
    f4b5:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    f4bd:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
    f4c6:	0f 85 97 00 00 00    	jne    f563 <within+0x293>
    f4cc:	48 81 c4 d8 00 00 00 	add    $0xd8,%rsp
    f4d3:	5b                   	pop    %rbx
    f4d4:	5d                   	pop    %rbp
    f4d5:	41 5c                	pop    %r12
    f4d7:	41 5d                	pop    %r13
    f4d9:	41 5e                	pop    %r14
    f4db:	41 5f                	pop    %r15
    f4dd:	c3                   	ret
    f4de:	66 90                	xchg   %ax,%ax
  return 0;
    f4e0:	31 c0                	xor    %eax,%eax
    f4e2:	eb b3                	jmp    f497 <within+0x1c7>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f4e4:	e8 f7 4f ff ff       	call   44e0 <__asan_report_load8@plt>
    f4e9:	e8 f2 4f ff ff       	call   44e0 <__asan_report_load8@plt>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    f4ee:	e8 ed 4f ff ff       	call   44e0 <__asan_report_load8@plt>
    f4f3:	e8 e8 4f ff ff       	call   44e0 <__asan_report_load8@plt>
    f4f8:	e8 e3 4f ff ff       	call   44e0 <__asan_report_load8@plt>
    f4fd:	e8 de 4f ff ff       	call   44e0 <__asan_report_load8@plt>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f502:	e8 d9 4f ff ff       	call   44e0 <__asan_report_load8@plt>
    f507:	e8 d4 4f ff ff       	call   44e0 <__asan_report_load8@plt>
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    f50c:	bf a0 00 00 00       	mov    $0xa0,%edi
    f511:	4c 89 04 24          	mov    %r8,(%rsp)
    f515:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    f51a:	e8 b1 4f ff ff       	call   44d0 <__asan_stack_malloc_2@plt>
    f51f:	4c 8b 04 24          	mov    (%rsp),%r8
    f523:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    f528:	48 85 c0             	test   %rax,%rax
    f52b:	48 0f 45 d8          	cmovne %rax,%rbx
    f52f:	e9 d3 fd ff ff       	jmp    f307 <within+0x37>
    f534:	66 0f 6f 05 64 2f 00 00 	movdqa 0x2f64(%rip),%xmm0        # 124a0 <_IO_stdin_used+0x24a0>
    f53c:	48 c7 03 0e 36 e0 45 	movq   $0x45e0360e,(%rbx)
    f543:	c7 81 10 80 ff 7f f5 f5 f5 f5 	movl   $0xf5f5f5f5,0x7fff8010(%rcx)
    f54d:	0f 11 81 00 80 ff 7f 	movups %xmm0,0x7fff8000(%rcx)
    f554:	48 8b 93 f8 00 00 00 	mov    0xf8(%rbx),%rdx
    f55b:	c6 02 00             	movb   $0x0,(%rdx)
    f55e:	e9 52 ff ff ff       	jmp    f4b5 <within+0x1e5>
}
    f563:	e8 48 51 ff ff       	call   46b0 <__stack_chk_fail@plt>
    f568:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

000000000000f570 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    f570:	f3 0f 1e fa          	endbr64
    f574:	41 55                	push   %r13
    f576:	41 54                	push   %r12
    f578:	55                   	push   %rbp
    f579:	53                   	push   %rbx
    f57a:	48 81 ec c8 00 00 00 	sub    $0xc8,%rsp
    f581:	8b 05 f9 65 00 00    	mov    0x65f9(%rip),%eax        # 15b80 <__asan_option_detect_stack_use_after_return@@Base>
    f587:	48 89 e3             	mov    %rsp,%rbx
    f58a:	48 89 dd             	mov    %rbx,%rbp
    f58d:	85 c0                	test   %eax,%eax
    f58f:	0f 85 e1 02 00 00    	jne    f876 <overlap+0x306>
    f595:	48 8d 3d 5c 2b 00 00 	lea    0x2b5c(%rip),%rdi        # 120f8 <_IO_stdin_used+0x20f8>
    f59c:	48 89 da             	mov    %rbx,%rdx
    f59f:	48 c7 03 b3 8a b5 41 	movq   $0x41b58ab3,(%rbx)
    f5a6:	48 8d 83 c0 00 00 00 	lea    0xc0(%rbx),%rax
    f5ad:	48 89 7b 08          	mov    %rdi,0x8(%rbx)
    f5b1:	48 c1 ea 03          	shr    $0x3,%rdx
    f5b5:	48 8d 3d b4 ff ff ff 	lea    -0x4c(%rip),%rdi        # f570 <overlap>
    f5bc:	48 89 7b 10          	mov    %rdi,0x10(%rbx)
  return left.tv_sec > right.tv_sec &&
    f5c0:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
int overlap(struct Snapshot left, struct Snapshot right) {
    f5c4:	f3 0f 6f 8c 24 f0 00 00 00 	movdqu 0xf0(%rsp),%xmm1
    f5cd:	c7 82 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%rdx)
  return left.tv_sec > right.tv_sec &&
    f5d7:	48 89 fe             	mov    %rdi,%rsi
int overlap(struct Snapshot left, struct Snapshot right) {
    f5da:	f3 0f 6f 94 24 00 01 00 00 	movdqu 0x100(%rsp),%xmm2
    f5e3:	c7 82 08 80 ff 7f f2 f2 f2 f2 	movl   $0xf2f2f2f2,0x7fff8008(%rdx)
  return left.tv_sec > right.tv_sec &&
    f5ed:	48 c1 ee 03          	shr    $0x3,%rsi
int overlap(struct Snapshot left, struct Snapshot right) {
    f5f1:	f3 0f 6f 9c 24 10 01 00 00 	movdqu 0x110(%rsp),%xmm3
    f5fa:	c7 82 10 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff8010(%rdx)
    f604:	f3 0f 6f a4 24 20 01 00 00 	movdqu 0x120(%rsp),%xmm4
    f60d:	64 48 8b 0c 25 28 00 00 00 	mov    %fs:0x28,%rcx
    f616:	48 89 8c 24 b8 00 00 00 	mov    %rcx,0xb8(%rsp)
    f61e:	31 c9                	xor    %ecx,%ecx
  return left.tv_sec > right.tv_sec &&
    f620:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
int overlap(struct Snapshot left, struct Snapshot right) {
    f627:	0f 11 58 a0          	movups %xmm3,-0x60(%rax)
  return left.tv_sec > right.tv_sec &&
    f62b:	48 8d 4b 20          	lea    0x20(%rbx),%rcx
int overlap(struct Snapshot left, struct Snapshot right) {
    f62f:	0f 11 88 60 ff ff ff 	movups %xmm1,-0xa0(%rax)
    f636:	0f 11 90 70 ff ff ff 	movups %xmm2,-0x90(%rax)
    f63d:	0f 11 60 b0          	movups %xmm4,-0x50(%rax)
  return left.tv_sec > right.tv_sec &&
    f641:	0f 85 db 01 00 00    	jne    f822 <overlap+0x2b2>
         left.tv_nsec > right.tv_nsec;
    f647:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    f64b:	4c 8b 90 70 ff ff ff 	mov    -0x90(%rax),%r10
    f652:	48 89 fe             	mov    %rdi,%rsi
    f655:	48 c1 ee 03          	shr    $0x3,%rsi
    f659:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    f660:	0f 85 b7 01 00 00    	jne    f81d <overlap+0x2ad>
  return left.tv_sec > right.tv_sec &&
    f666:	48 8d 73 70          	lea    0x70(%rbx),%rsi
    f66a:	4c 8b 98 78 ff ff ff 	mov    -0x88(%rax),%r11
    f671:	48 8d 7b 60          	lea    0x60(%rbx),%rdi
    f675:	49 89 f0             	mov    %rsi,%r8
    f678:	49 c1 e8 03          	shr    $0x3,%r8
    f67c:	41 80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r8)
    f684:	0f 85 b5 01 00 00    	jne    f83f <overlap+0x2cf>
         left.tv_nsec > right.tv_nsec;
    f68a:	48 8d 73 78          	lea    0x78(%rbx),%rsi
    f68e:	4c 8b 48 b0          	mov    -0x50(%rax),%r9
    f692:	49 89 f0             	mov    %rsi,%r8
    f695:	49 c1 e8 03          	shr    $0x3,%r8
    f699:	41 80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r8)
    f6a1:	0f 85 90 01 00 00    	jne    f837 <overlap+0x2c7>
  return left.tv_sec > right.tv_sec &&
    f6a7:	48 89 ce             	mov    %rcx,%rsi
    f6aa:	4c 8b 60 b8          	mov    -0x48(%rax),%r12
    f6ae:	48 c1 ee 03          	shr    $0x3,%rsi
    f6b2:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    f6b9:	0f 85 70 01 00 00    	jne    f82f <overlap+0x2bf>
         left.tv_nsec > right.tv_nsec;
    f6bf:	48 8d 4b 28          	lea    0x28(%rbx),%rcx
    f6c3:	4c 8b 80 60 ff ff ff 	mov    -0xa0(%rax),%r8
    f6ca:	48 89 ce             	mov    %rcx,%rsi
    f6cd:	48 c1 ee 03          	shr    $0x3,%rsi
    f6d1:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    f6d8:	0f 85 49 01 00 00    	jne    f827 <overlap+0x2b7>
  return left.tv_sec > right.tv_sec &&
    f6de:	48 89 f9             	mov    %rdi,%rcx
    f6e1:	48 8b b0 68 ff ff ff 	mov    -0x98(%rax),%rsi
    f6e8:	48 c1 e9 03          	shr    $0x3,%rcx
    f6ec:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    f6f3:	0f 85 1f 01 00 00    	jne    f818 <overlap+0x2a8>
         left.tv_nsec > right.tv_nsec;
    f6f9:	48 8d 4b 68          	lea    0x68(%rbx),%rcx
    f6fd:	48 8b 78 a0          	mov    -0x60(%rax),%rdi
    f701:	49 89 cd             	mov    %rcx,%r13
    f704:	49 c1 ed 03          	shr    $0x3,%r13
    f708:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    f710:	0f 85 fa 00 00 00    	jne    f810 <overlap+0x2a0>
    f716:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
  return left.tv_sec > right.tv_sec &&
    f71a:	4c 39 c7             	cmp    %r8,%rdi
    f71d:	7d 29                	jge    f748 <overlap+0x1d8>
    f71f:	48 39 f1             	cmp    %rsi,%rcx
    f722:	7d 5c                	jge    f780 <overlap+0x210>
    f724:	4d 39 e3             	cmp    %r12,%r11
    f727:	7d 0a                	jge    f733 <overlap+0x1c3>
    return 1;
    f729:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    f72e:	4d 39 ca             	cmp    %r9,%r10
    f731:	7c 51                	jl     f784 <overlap+0x214>
  return 0;
    f733:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f735:	4d 39 ca             	cmp    %r9,%r10
    f738:	7f 4a                	jg     f784 <overlap+0x214>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    f73a:	31 c0                	xor    %eax,%eax
    f73c:	4d 39 e3             	cmp    %r12,%r11
    f73f:	0f 9e c0             	setle  %al
    f742:	eb 40                	jmp    f784 <overlap+0x214>
    f744:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    f748:	0f 8e a2 00 00 00    	jle    f7f0 <overlap+0x280>
    f74e:	48 39 f1             	cmp    %rsi,%rcx
    f751:	7f 7d                	jg     f7d0 <overlap+0x260>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f753:	75 2d                	jne    f782 <overlap+0x212>
    f755:	4d 39 ca             	cmp    %r9,%r10
    f758:	7c 28                	jl     f782 <overlap+0x212>
    return 1;
    f75a:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    f75f:	4d 39 e3             	cmp    %r12,%r11
    f762:	7d 20                	jge    f784 <overlap+0x214>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f764:	48 39 f1             	cmp    %rsi,%rcx
    f767:	0f 94 c1             	sete   %cl
    f76a:	4c 39 c7             	cmp    %r8,%rdi
    f76d:	0f 94 c0             	sete   %al
    f770:	21 c1                	and    %eax,%ecx
    f772:	31 c0                	xor    %eax,%eax
    f774:	4d 39 ca             	cmp    %r9,%r10
    f777:	0f 94 c0             	sete   %al
    f77a:	21 c8                	and    %ecx,%eax
    f77c:	eb 06                	jmp    f784 <overlap+0x214>
    f77e:	66 90                	xchg   %ax,%ax
    f780:	74 b1                	je     f733 <overlap+0x1c3>
  return 0;
    f782:	31 c0                	xor    %eax,%eax
int overlap(struct Snapshot left, struct Snapshot right) {
    f784:	48 39 dd             	cmp    %rbx,%rbp
    f787:	0f 85 ba 00 00 00    	jne    f847 <overlap+0x2d7>
    f78d:	c7 82 00 80 ff 7f 00 00 00 00 	movl   $0x0,0x7fff8000(%rdx)
    f797:	c7 82 08 80 ff 7f 00 00 00 00 	movl   $0x0,0x7fff8008(%rdx)
    f7a1:	c7 82 10 80 ff 7f 00 00 00 00 	movl   $0x0,0x7fff8010(%rdx)
}
    f7ab:	48 8b 94 24 b8 00 00 00 	mov    0xb8(%rsp),%rdx
    f7b3:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
    f7bc:	0f 85 ca 00 00 00    	jne    f88c <overlap+0x31c>
    f7c2:	48 81 c4 c8 00 00 00 	add    $0xc8,%rsp
    f7c9:	5b                   	pop    %rbx
    f7ca:	5d                   	pop    %rbp
    f7cb:	41 5c                	pop    %r12
    f7cd:	41 5d                	pop    %r13
    f7cf:	c3                   	ret
  return left.tv_sec > right.tv_sec &&
    f7d0:	4d 39 e3             	cmp    %r12,%r11
    f7d3:	0f 8e 7c ff ff ff    	jle    f755 <overlap+0x1e5>
    return 1;
    f7d9:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    f7de:	4d 39 ca             	cmp    %r9,%r10
    f7e1:	0f 8e 6e ff ff ff    	jle    f755 <overlap+0x1e5>
    f7e7:	eb 9b                	jmp    f784 <overlap+0x214>
    f7e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f7f0:	48 39 f1             	cmp    %rsi,%rcx
    f7f3:	0f 8c 3a ff ff ff    	jl     f733 <overlap+0x1c3>
    f7f9:	4d 39 ca             	cmp    %r9,%r10
    f7fc:	0f 8d 58 ff ff ff    	jge    f75a <overlap+0x1ea>
    f802:	48 39 f1             	cmp    %rsi,%rcx
    f805:	0f 84 2f ff ff ff    	je     f73a <overlap+0x1ca>
    f80b:	e9 72 ff ff ff       	jmp    f782 <overlap+0x212>
         left.tv_nsec > right.tv_nsec;
    f810:	48 89 cf             	mov    %rcx,%rdi
    f813:	e8 c8 4c ff ff       	call   44e0 <__asan_report_load8@plt>
  return left.tv_sec > right.tv_sec &&
    f818:	e8 c3 4c ff ff       	call   44e0 <__asan_report_load8@plt>
         left.tv_nsec > right.tv_nsec;
    f81d:	e8 be 4c ff ff       	call   44e0 <__asan_report_load8@plt>
  return left.tv_sec > right.tv_sec &&
    f822:	e8 b9 4c ff ff       	call   44e0 <__asan_report_load8@plt>
         left.tv_nsec > right.tv_nsec;
    f827:	48 89 cf             	mov    %rcx,%rdi
    f82a:	e8 b1 4c ff ff       	call   44e0 <__asan_report_load8@plt>
  return left.tv_sec > right.tv_sec &&
    f82f:	48 89 cf             	mov    %rcx,%rdi
    f832:	e8 a9 4c ff ff       	call   44e0 <__asan_report_load8@plt>
         left.tv_nsec > right.tv_nsec;
    f837:	48 89 f7             	mov    %rsi,%rdi
    f83a:	e8 a1 4c ff ff       	call   44e0 <__asan_report_load8@plt>
  return left.tv_sec > right.tv_sec &&
    f83f:	48 89 f7             	mov    %rsi,%rdi
    f842:	e8 99 4c ff ff       	call   44e0 <__asan_report_load8@plt>
int overlap(struct Snapshot left, struct Snapshot right) {
    f847:	66 0f 6f 05 51 2c 00 00 	movdqa 0x2c51(%rip),%xmm0        # 124a0 <_IO_stdin_used+0x24a0>
    f84f:	48 c7 03 0e 36 e0 45 	movq   $0x45e0360e,(%rbx)
    f856:	c7 82 10 80 ff 7f f5 f5 f5 f5 	movl   $0xf5f5f5f5,0x7fff8010(%rdx)
    f860:	0f 11 82 00 80 ff 7f 	movups %xmm0,0x7fff8000(%rdx)
    f867:	48 8b 93 f8 00 00 00 	mov    0xf8(%rbx),%rdx
    f86e:	c6 02 00             	movb   $0x0,(%rdx)
    f871:	e9 35 ff ff ff       	jmp    f7ab <overlap+0x23b>
    f876:	bf a0 00 00 00       	mov    $0xa0,%edi
    f87b:	e8 50 4c ff ff       	call   44d0 <__asan_stack_malloc_2@plt>
    f880:	48 85 c0             	test   %rax,%rax
    f883:	48 0f 45 d8          	cmovne %rax,%rbx
    f887:	e9 09 fd ff ff       	jmp    f595 <overlap+0x25>
}
    f88c:	e8 1f 4e ff ff       	call   46b0 <__stack_chk_fail@plt>
    f891:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    f89c:	0f 1f 40 00          	nopl   0x0(%rax)

000000000000f8a0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    f8a0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    f8a4:	85 f6                	test   %esi,%esi
    f8a6:	0f 8e e4 06 00 00    	jle    ff90 <verify+0x6f0>
int verify(struct KernelThread *thread_data, int thread_count) {
    f8ac:	41 57                	push   %r15
    f8ae:	48 89 f8             	mov    %rdi,%rax
    f8b1:	41 89 f7             	mov    %esi,%r15d
    f8b4:	41 56                	push   %r14
    f8b6:	48 83 c0 38          	add    $0x38,%rax
  for (int x = 0 ; x < thread_count; x++) {
    f8ba:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    f8bd:	41 55                	push   %r13
    f8bf:	41 54                	push   %r12
    f8c1:	55                   	push   %rbp
    f8c2:	53                   	push   %rbx
    f8c3:	48 83 ec 78          	sub    $0x78,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    f8c7:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    f8cc:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    f8d1:	31 db                	xor    %ebx,%ebx
    f8d3:	44 89 74 24 4c       	mov    %r14d,0x4c(%rsp)
    f8d8:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
      if (z != x)  {
    f8dd:	39 5c 24 4c          	cmp    %ebx,0x4c(%rsp)
    f8e1:	0f 84 61 05 00 00    	je     fe48 <verify+0x5a8>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    f8e7:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    f8ec:	4c 8d 40 08          	lea    0x8(%rax),%r8
    f8f0:	4c 89 c2             	mov    %r8,%rdx
    f8f3:	48 c1 ea 03          	shr    $0x3,%rdx
    f8f7:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    f8fe:	84 d2                	test   %dl,%dl
    f900:	74 09                	je     f90b <verify+0x6b>
    f902:	80 fa 03             	cmp    $0x3,%dl
    f905:	0f 8e 9a 06 00 00    	jle    ffa5 <verify+0x705>
    f90b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    f910:	8b 50 08             	mov    0x8(%rax),%edx
    f913:	85 d2                	test   %edx,%edx
    f915:	0f 8e 2d 05 00 00    	jle    fe48 <verify+0x5a8>
    f91b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    f920:	89 5c 24 58          	mov    %ebx,0x58(%rsp)
    f924:	45 31 ed             	xor    %r13d,%r13d
    f927:	4d 89 c6             	mov    %r8,%r14
    f92a:	44 89 7c 24 5c       	mov    %r15d,0x5c(%rsp)
    f92f:	4d 89 e8             	mov    %r13,%r8
    f932:	4c 8d 60 08          	lea    0x8(%rax),%r12
    f936:	8b 54 24 4c          	mov    0x4c(%rsp),%edx
    f93a:	31 c0                	xor    %eax,%eax
    f93c:	bf 01 00 00 00       	mov    $0x1,%edi
    f941:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    f946:	48 8d 35 13 16 00 00 	lea    0x1613(%rip),%rsi        # 10f60 <_IO_stdin_used+0xf60>
    f94d:	e8 ce 4b ff ff       	call   4520 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    f952:	4c 89 e0             	mov    %r12,%rax
    f955:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    f95a:	48 c1 e8 03          	shr    $0x3,%rax
    f95e:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    f965:	84 c0                	test   %al,%al
    f967:	74 08                	je     f971 <verify+0xd1>
    f969:	3c 03                	cmp    $0x3,%al
    f96b:	0f 8e 22 06 00 00    	jle    ff93 <verify+0x6f3>
    f971:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    f976:	8b 40 08             	mov    0x8(%rax),%eax
    f979:	85 c0                	test   %eax,%eax
    f97b:	0f 8e 91 04 00 00    	jle    fe12 <verify+0x572>
    f981:	4c 89 c0             	mov    %r8,%rax
    f984:	48 c1 e0 09          	shl    $0x9,%rax
    f988:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    f98d:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    f992:	48 c1 e8 03          	shr    $0x3,%rax
    f996:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    f99d:	0f 85 f8 05 00 00    	jne    ff9b <verify+0x6fb>
    f9a3:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    f9a8:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
    f9ad:	4c 89 74 24 60       	mov    %r14,0x60(%rsp)
    f9b2:	31 db                	xor    %ebx,%ebx
    f9b4:	4c 89 44 24 68       	mov    %r8,0x68(%rsp)
    f9b9:	48 03 28             	add    (%rax),%rbp
    f9bc:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    f9c1:	4c 89 64 24 40       	mov    %r12,0x40(%rsp)
    f9c6:	48 c1 e8 03          	shr    $0x3,%rax
    f9ca:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    f9cf:	90                   	nop
    f9d0:	48 8d bd 60 01 00 00 	lea    0x160(%rbp),%rdi
    f9d7:	48 89 f8             	mov    %rdi,%rax
    f9da:	48 c1 e8 03          	shr    $0x3,%rax
    f9de:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    f9e5:	0f 85 2c 05 00 00    	jne    ff17 <verify+0x677>
    f9eb:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    f9f0:	48 8b 8d 60 01 00 00 	mov    0x160(%rbp),%rcx
    f9f7:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    f9fe:	0f 85 5f 05 00 00    	jne    ff63 <verify+0x6c3>
    fa04:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    fa09:	48 89 d8             	mov    %rbx,%rax
    fa0c:	48 c1 e0 09          	shl    $0x9,%rax
    fa10:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    fa15:	48 03 06             	add    (%rsi),%rax
    fa18:	48 8d b8 60 01 00 00 	lea    0x160(%rax),%rdi
    fa1f:	48 89 fa             	mov    %rdi,%rdx
    fa22:	48 c1 ea 03          	shr    $0x3,%rdx
    fa26:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    fa2d:	0f 85 2b 05 00 00    	jne    ff5e <verify+0x6be>
    fa33:	48 8b 90 60 01 00 00 	mov    0x160(%rax),%rdx
    fa3a:	48 8d 35 5f 15 00 00 	lea    0x155f(%rip),%rsi        # 10fa0 <_IO_stdin_used+0xfa0>
    fa41:	31 c0                	xor    %eax,%eax
    fa43:	bf 01 00 00 00       	mov    $0x1,%edi
    fa48:	e8 d3 4a ff ff       	call   4520 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    fa4d:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    fa52:	48 c1 e8 03          	shr    $0x3,%rax
    fa56:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fa5d:	0f 85 0a 05 00 00    	jne    ff6d <verify+0x6cd>
    fa63:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    fa68:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
    fa6d:	48 03 28             	add    (%rax),%rbp
    fa70:	48 8d bd 60 01 00 00 	lea    0x160(%rbp),%rdi
    fa77:	48 89 f8             	mov    %rdi,%rax
    fa7a:	48 c1 e8 03          	shr    $0x3,%rax
    fa7e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fa85:	0f 85 ce 04 00 00    	jne    ff59 <verify+0x6b9>
    fa8b:	48 8b 85 60 01 00 00 	mov    0x160(%rbp),%rax
    fa92:	48 85 c0             	test   %rax,%rax
    fa95:	0f 8e 3a 03 00 00    	jle    fdd5 <verify+0x535>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    fa9b:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    faa0:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    faa7:	0f 85 6f 04 00 00    	jne    ff1c <verify+0x67c>
    faad:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    fab2:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
    fab7:	48 89 5c 24 38       	mov    %rbx,0x38(%rsp)
    fabc:	41 bd 01 00 00 00    	mov    $0x1,%r13d
    fac2:	48 03 16             	add    (%rsi),%rdx
    fac5:	0f 1f 00             	nopl   (%rax)
    fac8:	48 8d ba 60 01 00 00 	lea    0x160(%rdx),%rdi
    facf:	48 89 f9             	mov    %rdi,%rcx
    fad2:	48 c1 e9 03          	shr    $0x3,%rcx
    fad6:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    fadd:	0f 85 4d 04 00 00    	jne    ff30 <verify+0x690>
    fae3:	4c 8b b2 60 01 00 00 	mov    0x160(%rdx),%r14
    faea:	4d 85 f6             	test   %r14,%r14
    faed:	0f 8e 75 03 00 00    	jle    fe68 <verify+0x5c8>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    faf3:	4d 89 ec             	mov    %r13,%r12
    faf6:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
    fafb:	31 db                	xor    %ebx,%ebx
    fafd:	49 c1 e4 05          	shl    $0x5,%r12
    fb01:	49 83 ec 20          	sub    $0x20,%r12
    fb05:	eb 36                	jmp    fb3d <verify+0x29d>
    fb07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    fb10:	4c 39 c1             	cmp    %r8,%rcx
    fb13:	0f 8d 57 02 00 00    	jge    fd70 <verify+0x4d0>
    fb19:	4d 39 cd             	cmp    %r9,%r13
    fb1c:	7d 09                	jge    fb27 <verify+0x287>
    fb1e:	4d 39 da             	cmp    %r11,%r10
    fb21:	0f 8f 89 01 00 00    	jg     fcb0 <verify+0x410>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    fb27:	4d 39 da             	cmp    %r11,%r10
    fb2a:	0f 8d 8b 02 00 00    	jge    fdbb <verify+0x51b>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    fb30:	48 83 c3 01          	add    $0x1,%rbx
    fb34:	49 39 de             	cmp    %rbx,%r14
    fb37:	0f 8e fd 01 00 00    	jle    fd3a <verify+0x49a>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    fb3d:	48 8d ba 50 01 00 00 	lea    0x150(%rdx),%rdi
    fb44:	48 89 f8             	mov    %rdi,%rax
    fb47:	48 c1 e8 03          	shr    $0x3,%rax
    fb4b:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fb52:	0f 85 9c 03 00 00    	jne    fef4 <verify+0x654>
    fb58:	48 8d bd 50 01 00 00 	lea    0x150(%rbp),%rdi
    fb5f:	49 89 df             	mov    %rbx,%r15
    fb62:	48 89 f8             	mov    %rdi,%rax
    fb65:	49 c1 e7 05          	shl    $0x5,%r15
    fb69:	4c 03 ba 50 01 00 00 	add    0x150(%rdx),%r15
    fb70:	48 c1 e8 03          	shr    $0x3,%rax
    fb74:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fb7b:	0f 85 6e 03 00 00    	jne    feef <verify+0x64f>
    fb81:	48 8b bd 50 01 00 00 	mov    0x150(%rbp),%rdi
    fb88:	4c 01 e7             	add    %r12,%rdi
  return left.tv_sec > right.tv_sec &&
    fb8b:	48 89 f8             	mov    %rdi,%rax
    fb8e:	48 c1 e8 03          	shr    $0x3,%rax
    fb92:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fb99:	0f 85 4b 03 00 00    	jne    feea <verify+0x64a>
         left.tv_nsec > right.tv_nsec;
    fb9f:	48 8d 4f 08          	lea    0x8(%rdi),%rcx
    fba3:	48 8b 37             	mov    (%rdi),%rsi
    fba6:	48 89 c8             	mov    %rcx,%rax
    fba9:	48 c1 e8 03          	shr    $0x3,%rax
    fbad:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fbb4:	0f 85 28 03 00 00    	jne    fee2 <verify+0x642>
  return left.tv_sec > right.tv_sec &&
    fbba:	48 8d 4f 10          	lea    0x10(%rdi),%rcx
    fbbe:	4c 8b 47 08          	mov    0x8(%rdi),%r8
    fbc2:	48 89 c8             	mov    %rcx,%rax
    fbc5:	48 c1 e8 03          	shr    $0x3,%rax
    fbc9:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fbd0:	0f 85 04 03 00 00    	jne    feda <verify+0x63a>
         left.tv_nsec > right.tv_nsec;
    fbd6:	48 8d 4f 18          	lea    0x18(%rdi),%rcx
    fbda:	4c 8b 5f 10          	mov    0x10(%rdi),%r11
    fbde:	48 89 c8             	mov    %rcx,%rax
    fbe1:	48 c1 e8 03          	shr    $0x3,%rax
    fbe5:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fbec:	0f 85 e0 02 00 00    	jne    fed2 <verify+0x632>
  return left.tv_sec > right.tv_sec &&
    fbf2:	4c 89 f8             	mov    %r15,%rax
    fbf5:	4c 8b 6f 18          	mov    0x18(%rdi),%r13
    fbf9:	48 c1 e8 03          	shr    $0x3,%rax
    fbfd:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fc04:	0f 85 c0 02 00 00    	jne    feca <verify+0x62a>
         left.tv_nsec > right.tv_nsec;
    fc0a:	4d 8d 4f 08          	lea    0x8(%r15),%r9
    fc0e:	49 8b 3f             	mov    (%r15),%rdi
    fc11:	4c 89 c8             	mov    %r9,%rax
    fc14:	48 c1 e8 03          	shr    $0x3,%rax
    fc18:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fc1f:	0f 85 9d 02 00 00    	jne    fec2 <verify+0x622>
  return left.tv_sec > right.tv_sec &&
    fc25:	4d 8d 57 10          	lea    0x10(%r15),%r10
    fc29:	49 8b 4f 08          	mov    0x8(%r15),%rcx
    fc2d:	4c 89 d0             	mov    %r10,%rax
    fc30:	48 c1 e8 03          	shr    $0x3,%rax
    fc34:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fc3b:	0f 85 79 02 00 00    	jne    feba <verify+0x61a>
         left.tv_nsec > right.tv_nsec;
    fc41:	49 8d 47 18          	lea    0x18(%r15),%rax
    fc45:	4d 8b 57 10          	mov    0x10(%r15),%r10
    fc49:	49 89 c1             	mov    %rax,%r9
    fc4c:	49 c1 e9 03          	shr    $0x3,%r9
    fc50:	41 80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r9)
    fc58:	0f 85 54 02 00 00    	jne    feb2 <verify+0x612>
    fc5e:	4d 8b 4f 18          	mov    0x18(%r15),%r9
  return left.tv_sec > right.tv_sec &&
    fc62:	48 39 f7             	cmp    %rsi,%rdi
    fc65:	0f 8c a5 fe ff ff    	jl     fb10 <verify+0x270>
    fc6b:	0f 8e 2f 01 00 00    	jle    fda0 <verify+0x500>
    fc71:	4c 39 c1             	cmp    %r8,%rcx
    fc74:	0f 8f 06 01 00 00    	jg     fd80 <verify+0x4e0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    fc7a:	0f 85 b0 fe ff ff    	jne    fb30 <verify+0x290>
    fc80:	4d 39 da             	cmp    %r11,%r10
    fc83:	0f 8f a7 fe ff ff    	jg     fb30 <verify+0x290>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    fc89:	4d 39 cd             	cmp    %r9,%r13
    fc8c:	7d 22                	jge    fcb0 <verify+0x410>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    fc8e:	4c 39 c1             	cmp    %r8,%rcx
    fc91:	0f 94 c1             	sete   %cl
    fc94:	48 39 f7             	cmp    %rsi,%rdi
    fc97:	0f 94 c0             	sete   %al
    fc9a:	84 c1                	test   %al,%cl
    fc9c:	0f 84 8e fe ff ff    	je     fb30 <verify+0x290>
    fca2:	4d 39 da             	cmp    %r11,%r10
    fca5:	0f 85 85 fe ff ff    	jne    fb30 <verify+0x290>
    fcab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    fcb0:	48 89 f2             	mov    %rsi,%rdx
    fcb3:	31 c0                	xor    %eax,%eax
    fcb5:	4c 89 d1             	mov    %r10,%rcx
    fcb8:	bf 01 00 00 00       	mov    $0x1,%edi
    fcbd:	48 8d 35 1c 13 00 00 	lea    0x131c(%rip),%rsi        # 10fe0 <_IO_stdin_used+0xfe0>
    fcc4:	e8 57 48 ff ff       	call   4520 <__printf_chk@plt>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    fcc9:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    fcce:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fcd5:	0f 85 2d 02 00 00    	jne    ff08 <verify+0x668>
    fcdb:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    fce0:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
    fce5:	48 03 10             	add    (%rax),%rdx
    fce8:	48 8d ba 60 01 00 00 	lea    0x160(%rdx),%rdi
    fcef:	48 89 f8             	mov    %rdi,%rax
    fcf2:	48 c1 e8 03          	shr    $0x3,%rax
    fcf6:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fcfd:	0f 85 00 02 00 00    	jne    ff03 <verify+0x663>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    fd03:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    fd08:	4c 8b b2 60 01 00 00 	mov    0x160(%rdx),%r14
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    fd0f:	48 c1 e8 03          	shr    $0x3,%rax
    fd13:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fd1a:	0f 85 d9 01 00 00    	jne    fef9 <verify+0x659>
    fd20:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    fd25:	48 83 c3 01          	add    $0x1,%rbx
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    fd29:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
    fd2e:	48 03 28             	add    (%rax),%rbp
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    fd31:	49 39 de             	cmp    %rbx,%r14
    fd34:	0f 8f 03 fe ff ff    	jg     fb3d <verify+0x29d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    fd3a:	48 8d bd 60 01 00 00 	lea    0x160(%rbp),%rdi
    fd41:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
    fd46:	48 89 f8             	mov    %rdi,%rax
    fd49:	48 c1 e8 03          	shr    $0x3,%rax
    fd4d:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fd54:	0f 85 b8 01 00 00    	jne    ff12 <verify+0x672>
    fd5a:	48 8b 85 60 01 00 00 	mov    0x160(%rbp),%rax
    fd61:	49 39 c5             	cmp    %rax,%r13
    fd64:	7d 6a                	jge    fdd0 <verify+0x530>
    fd66:	49 83 c5 01          	add    $0x1,%r13
    fd6a:	e9 59 fd ff ff       	jmp    fac8 <verify+0x228>
    fd6f:	90                   	nop
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    fd70:	0f 85 ba fd ff ff    	jne    fb30 <verify+0x290>
    fd76:	e9 ac fd ff ff       	jmp    fb27 <verify+0x287>
    fd7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    fd80:	4d 39 cd             	cmp    %r9,%r13
    fd83:	0f 8e f7 fe ff ff    	jle    fc80 <verify+0x3e0>
    fd89:	4d 39 da             	cmp    %r11,%r10
    fd8c:	0f 8d ee fe ff ff    	jge    fc80 <verify+0x3e0>
    fd92:	e9 19 ff ff ff       	jmp    fcb0 <verify+0x410>
    fd97:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    fda0:	4c 39 c1             	cmp    %r8,%rcx
    fda3:	0f 8c 7e fd ff ff    	jl     fb27 <verify+0x287>
    fda9:	4d 39 da             	cmp    %r11,%r10
    fdac:	0f 8e d7 fe ff ff    	jle    fc89 <verify+0x3e9>
    fdb2:	4c 39 c1             	cmp    %r8,%rcx
    fdb5:	0f 85 75 fd ff ff    	jne    fb30 <verify+0x290>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    fdbb:	4d 39 cd             	cmp    %r9,%r13
    fdbe:	0f 8f 6c fd ff ff    	jg     fb30 <verify+0x290>
    fdc4:	e9 e7 fe ff ff       	jmp    fcb0 <verify+0x410>
    fdc9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    fdd0:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    fdd5:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    fdda:	48 c1 e8 03          	shr    $0x3,%rax
    fdde:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    fde5:	84 c0                	test   %al,%al
    fde7:	74 08                	je     fdf1 <verify+0x551>
    fde9:	3c 03                	cmp    $0x3,%al
    fdeb:	0f 8e 35 01 00 00    	jle    ff26 <verify+0x686>
    fdf1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    fdf6:	48 83 c3 01          	add    $0x1,%rbx
    fdfa:	39 58 08             	cmp    %ebx,0x8(%rax)
    fdfd:	0f 8f cd fb ff ff    	jg     f9d0 <verify+0x130>
    fe03:	4c 8b 74 24 60       	mov    0x60(%rsp),%r14
    fe08:	4c 8b 44 24 68       	mov    0x68(%rsp),%r8
    fe0d:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    fe12:	4c 89 f0             	mov    %r14,%rax
    fe15:	48 c1 e8 03          	shr    $0x3,%rax
    fe19:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    fe20:	84 c0                	test   %al,%al
    fe22:	74 08                	je     fe2c <verify+0x58c>
    fe24:	3c 03                	cmp    $0x3,%al
    fe26:	0f 8e 5c 01 00 00    	jle    ff88 <verify+0x6e8>
    fe2c:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    fe31:	49 83 c0 01          	add    $0x1,%r8
    fe35:	44 39 40 08          	cmp    %r8d,0x8(%rax)
    fe39:	0f 8f f7 fa ff ff    	jg     f936 <verify+0x96>
    fe3f:	8b 5c 24 58          	mov    0x58(%rsp),%ebx
    fe43:	44 8b 7c 24 5c       	mov    0x5c(%rsp),%r15d
    for (int z = 0 ; z < thread_count; z++) {
    fe48:	48 81 44 24 10 c0 00 00 00 	addq   $0xc0,0x10(%rsp)
    fe51:	8d 53 01             	lea    0x1(%rbx),%edx
    fe54:	41 39 d7             	cmp    %edx,%r15d
    fe57:	0f 84 d8 00 00 00    	je     ff35 <verify+0x695>
    fe5d:	89 d3                	mov    %edx,%ebx
    fe5f:	e9 79 fa ff ff       	jmp    f8dd <verify+0x3d>
    fe64:	0f 1f 40 00          	nopl   0x0(%rax)
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    fe68:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    fe6d:	4c 39 e8             	cmp    %r13,%rax
    fe70:	0f 8e 5f ff ff ff    	jle    fdd5 <verify+0x535>
    fe76:	4d 63 ed             	movslq %r13d,%r13
    fe79:	4c 89 ea             	mov    %r13,%rdx
    fe7c:	49 83 c5 01          	add    $0x1,%r13
    fe80:	48 f7 d2             	not    %rdx
    fe83:	48 01 c2             	add    %rax,%rdx
    fe86:	83 e2 01             	and    $0x1,%edx
    fe89:	4c 39 e8             	cmp    %r13,%rax
    fe8c:	0f 8e 43 ff ff ff    	jle    fdd5 <verify+0x535>
    fe92:	48 85 d2             	test   %rdx,%rdx
    fe95:	74 0d                	je     fea4 <verify+0x604>
    fe97:	49 83 c5 01          	add    $0x1,%r13
    fe9b:	4c 39 e8             	cmp    %r13,%rax
    fe9e:	0f 8e 31 ff ff ff    	jle    fdd5 <verify+0x535>
    fea4:	49 83 c5 02          	add    $0x2,%r13
    fea8:	4c 39 e8             	cmp    %r13,%rax
    feab:	7f f7                	jg     fea4 <verify+0x604>
    fead:	e9 23 ff ff ff       	jmp    fdd5 <verify+0x535>
         left.tv_nsec > right.tv_nsec;
    feb2:	48 89 c7             	mov    %rax,%rdi
    feb5:	e8 26 46 ff ff       	call   44e0 <__asan_report_load8@plt>
  return left.tv_sec > right.tv_sec &&
    feba:	4c 89 d7             	mov    %r10,%rdi
    febd:	e8 1e 46 ff ff       	call   44e0 <__asan_report_load8@plt>
         left.tv_nsec > right.tv_nsec;
    fec2:	4c 89 cf             	mov    %r9,%rdi
    fec5:	e8 16 46 ff ff       	call   44e0 <__asan_report_load8@plt>
  return left.tv_sec > right.tv_sec &&
    feca:	4c 89 ff             	mov    %r15,%rdi
    fecd:	e8 0e 46 ff ff       	call   44e0 <__asan_report_load8@plt>
         left.tv_nsec > right.tv_nsec;
    fed2:	48 89 cf             	mov    %rcx,%rdi
    fed5:	e8 06 46 ff ff       	call   44e0 <__asan_report_load8@plt>
  return left.tv_sec > right.tv_sec &&
    feda:	48 89 cf             	mov    %rcx,%rdi
    fedd:	e8 fe 45 ff ff       	call   44e0 <__asan_report_load8@plt>
         left.tv_nsec > right.tv_nsec;
    fee2:	48 89 cf             	mov    %rcx,%rdi
    fee5:	e8 f6 45 ff ff       	call   44e0 <__asan_report_load8@plt>
  return left.tv_sec > right.tv_sec &&
    feea:	e8 f1 45 ff ff       	call   44e0 <__asan_report_load8@plt>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    feef:	e8 ec 45 ff ff       	call   44e0 <__asan_report_load8@plt>
    fef4:	e8 e7 45 ff ff       	call   44e0 <__asan_report_load8@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    fef9:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    fefe:	e8 dd 45 ff ff       	call   44e0 <__asan_report_load8@plt>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    ff03:	e8 d8 45 ff ff       	call   44e0 <__asan_report_load8@plt>
    ff08:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    ff0d:	e8 ce 45 ff ff       	call   44e0 <__asan_report_load8@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    ff12:	e8 c9 45 ff ff       	call   44e0 <__asan_report_load8@plt>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    ff17:	e8 c4 45 ff ff       	call   44e0 <__asan_report_load8@plt>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    ff1c:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    ff21:	e8 ba 45 ff ff       	call   44e0 <__asan_report_load8@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    ff26:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    ff2b:	e8 20 46 ff ff       	call   4550 <__asan_report_load4@plt>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    ff30:	e8 ab 45 ff ff       	call   44e0 <__asan_report_load8@plt>
    ff35:	44 8b 74 24 4c       	mov    0x4c(%rsp),%r14d
    ff3a:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
  for (int x = 0 ; x < thread_count; x++) {
    ff3f:	48 81 44 24 08 c0 00 00 00 	addq   $0xc0,0x8(%rsp)
    ff48:	41 8d 56 01          	lea    0x1(%r14),%edx
    ff4c:	41 39 de             	cmp    %ebx,%r14d
    ff4f:	74 26                	je     ff77 <verify+0x6d7>
    ff51:	41 89 d6             	mov    %edx,%r14d
    ff54:	e9 73 f9 ff ff       	jmp    f8cc <verify+0x2c>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    ff59:	e8 82 45 ff ff       	call   44e0 <__asan_report_load8@plt>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    ff5e:	e8 7d 45 ff ff       	call   44e0 <__asan_report_load8@plt>
    ff63:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    ff68:	e8 73 45 ff ff       	call   44e0 <__asan_report_load8@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    ff6d:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    ff72:	e8 69 45 ff ff       	call   44e0 <__asan_report_load8@plt>
}
    ff77:	48 83 c4 78          	add    $0x78,%rsp
    ff7b:	31 c0                	xor    %eax,%eax
    ff7d:	5b                   	pop    %rbx
    ff7e:	5d                   	pop    %rbp
    ff7f:	41 5c                	pop    %r12
    ff81:	41 5d                	pop    %r13
    ff83:	41 5e                	pop    %r14
    ff85:	41 5f                	pop    %r15
    ff87:	c3                   	ret
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    ff88:	4c 89 f7             	mov    %r14,%rdi
    ff8b:	e8 c0 45 ff ff       	call   4550 <__asan_report_load4@plt>
}
    ff90:	31 c0                	xor    %eax,%eax
    ff92:	c3                   	ret
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    ff93:	4c 89 e7             	mov    %r12,%rdi
    ff96:	e8 b5 45 ff ff       	call   4550 <__asan_report_load4@plt>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    ff9b:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    ffa0:	e8 3b 45 ff ff       	call   44e0 <__asan_report_load8@plt>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    ffa5:	4c 89 c7             	mov    %r8,%rdi
    ffa8:	e8 a3 45 ff ff       	call   4550 <__asan_report_load4@plt>

Disassembly of section .fini:

000000000000ffb0 <_fini>:
    ffb0:	f3 0f 1e fa          	endbr64
    ffb4:	48 83 ec 08          	sub    $0x8,%rsp
    ffb8:	48 83 c4 08          	add    $0x8,%rsp
    ffbc:	c3                   	ret
