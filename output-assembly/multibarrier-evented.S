
multibarrier-evented:     file format elf64-x86-64


Disassembly of section .init:

0000000000004000 <_init>:
    4000:	f3 0f 1e fa          	endbr64
    4004:	48 83 ec 08          	sub    $0x8,%rsp
    4008:	48 8b 05 c9 0f 01 00 	mov    0x10fc9(%rip),%rax        # 14fd8 <__gmon_start__@Base>
    400f:	48 85 c0             	test   %rax,%rax
    4012:	74 02                	je     4016 <_init+0x16>
    4014:	ff d0                	call   *%rax
    4016:	48 83 c4 08          	add    $0x8,%rsp
    401a:	c3                   	ret

Disassembly of section .plt:

0000000000004020 <.plt>:
    4020:	ff 35 a2 0d 01 00    	push   0x10da2(%rip)        # 14dc8 <_GLOBAL_OFFSET_TABLE_+0x8>
    4026:	ff 25 a4 0d 01 00    	jmp    *0x10da4(%rip)        # 14dd0 <_GLOBAL_OFFSET_TABLE_+0x10>
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
    4434:	ff 25 b6 0b 01 00    	jmp    *0x10bb6(%rip)        # 14ff0 <__cxa_finalize@GLIBC_2.2.5>
    443a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

0000000000004440 <pthread_setaffinity_np@plt>:
    4440:	f3 0f 1e fa          	endbr64
    4444:	ff 25 8e 09 01 00    	jmp    *0x1098e(%rip)        # 14dd8 <pthread_setaffinity_np@GLIBC_2.34>
    444a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004450 <__asan_poison_stack_memory@plt>:
    4450:	f3 0f 1e fa          	endbr64
    4454:	ff 25 86 09 01 00    	jmp    *0x10986(%rip)        # 14de0 <__asan_poison_stack_memory@Base>
    445a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004460 <calloc@plt>:
    4460:	f3 0f 1e fa          	endbr64
    4464:	ff 25 7e 09 01 00    	jmp    *0x1097e(%rip)        # 14de8 <calloc@Base>
    446a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004470 <io_uring_queue_init@plt>:
    4470:	f3 0f 1e fa          	endbr64
    4474:	ff 25 76 09 01 00    	jmp    *0x10976(%rip)        # 14df0 <io_uring_queue_init@LIBURING_2.0>
    447a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004480 <clock_gettime@plt>:
    4480:	f3 0f 1e fa          	endbr64
    4484:	ff 25 6e 09 01 00    	jmp    *0x1096e(%rip)        # 14df8 <clock_gettime@Base>
    448a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004490 <close@plt>:
    4490:	f3 0f 1e fa          	endbr64
    4494:	ff 25 66 09 01 00    	jmp    *0x10966(%rip)        # 14e00 <close@GLIBC_2.2.5>
    449a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000044a0 <fwrite@plt>:
    44a0:	f3 0f 1e fa          	endbr64
    44a4:	ff 25 5e 09 01 00    	jmp    *0x1095e(%rip)        # 14e08 <fwrite@Base>
    44aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000044b0 <__asan_init@plt>:
    44b0:	f3 0f 1e fa          	endbr64
    44b4:	ff 25 56 09 01 00    	jmp    *0x10956(%rip)        # 14e10 <__asan_init@Base>
    44ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000044c0 <memcpy@plt>:
    44c0:	f3 0f 1e fa          	endbr64
    44c4:	ff 25 4e 09 01 00    	jmp    *0x1094e(%rip)        # 14e18 <memcpy@Base>
    44ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000044d0 <__asan_stack_malloc_2@plt>:
    44d0:	f3 0f 1e fa          	endbr64
    44d4:	ff 25 46 09 01 00    	jmp    *0x10946(%rip)        # 14e20 <__asan_stack_malloc_2@Base>
    44da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000044e0 <__asan_report_load8@plt>:
    44e0:	f3 0f 1e fa          	endbr64
    44e4:	ff 25 3e 09 01 00    	jmp    *0x1093e(%rip)        # 14e28 <__asan_report_load8@Base>
    44ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000044f0 <__asan_stack_malloc_1@plt>:
    44f0:	f3 0f 1e fa          	endbr64
    44f4:	ff 25 36 09 01 00    	jmp    *0x10936(%rip)        # 14e30 <__asan_stack_malloc_1@Base>
    44fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004500 <__asan_report_store2@plt>:
    4500:	f3 0f 1e fa          	endbr64
    4504:	ff 25 2e 09 01 00    	jmp    *0x1092e(%rip)        # 14e38 <__asan_report_store2@Base>
    450a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004510 <exit@plt>:
    4510:	f3 0f 1e fa          	endbr64
    4514:	ff 25 26 09 01 00    	jmp    *0x10926(%rip)        # 14e40 <exit@GLIBC_2.2.5>
    451a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004520 <__printf_chk@plt>:
    4520:	f3 0f 1e fa          	endbr64
    4524:	ff 25 1e 09 01 00    	jmp    *0x1091e(%rip)        # 14e48 <__printf_chk@GLIBC_2.3.4>
    452a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004530 <putchar@plt>:
    4530:	f3 0f 1e fa          	endbr64
    4534:	ff 25 16 09 01 00    	jmp    *0x10916(%rip)        # 14e50 <putchar@GLIBC_2.2.5>
    453a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004540 <__asan_stack_malloc_6@plt>:
    4540:	f3 0f 1e fa          	endbr64
    4544:	ff 25 0e 09 01 00    	jmp    *0x1090e(%rip)        # 14e58 <__asan_stack_malloc_6@Base>
    454a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004550 <__asan_report_load4@plt>:
    4550:	f3 0f 1e fa          	endbr64
    4554:	ff 25 06 09 01 00    	jmp    *0x10906(%rip)        # 14e60 <__asan_report_load4@Base>
    455a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004560 <__asan_report_load_n@plt>:
    4560:	f3 0f 1e fa          	endbr64
    4564:	ff 25 fe 08 01 00    	jmp    *0x108fe(%rip)        # 14e68 <__asan_report_load_n@Base>
    456a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004570 <__asan_unpoison_stack_memory@plt>:
    4570:	f3 0f 1e fa          	endbr64
    4574:	ff 25 f6 08 01 00    	jmp    *0x108f6(%rip)        # 14e70 <__asan_unpoison_stack_memory@Base>
    457a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004580 <__asan_report_store_n@plt>:
    4580:	f3 0f 1e fa          	endbr64
    4584:	ff 25 ee 08 01 00    	jmp    *0x108ee(%rip)        # 14e78 <__asan_report_store_n@Base>
    458a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004590 <malloc@plt>:
    4590:	f3 0f 1e fa          	endbr64
    4594:	ff 25 e6 08 01 00    	jmp    *0x108e6(%rip)        # 14e80 <malloc@Base>
    459a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000045a0 <strrchr@plt>:
    45a0:	f3 0f 1e fa          	endbr64
    45a4:	ff 25 de 08 01 00    	jmp    *0x108de(%rip)        # 14e88 <strrchr@Base>
    45aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000045b0 <__memcpy_chk@plt>:
    45b0:	f3 0f 1e fa          	endbr64
    45b4:	ff 25 d6 08 01 00    	jmp    *0x108d6(%rip)        # 14e90 <__memcpy_chk@GLIBC_2.3.4>
    45ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000045c0 <setsockopt@plt>:
    45c0:	f3 0f 1e fa          	endbr64
    45c4:	ff 25 ce 08 01 00    	jmp    *0x108ce(%rip)        # 14e98 <setsockopt@GLIBC_2.2.5>
    45ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000045d0 <eventfd@plt>:
    45d0:	f3 0f 1e fa          	endbr64
    45d4:	ff 25 c6 08 01 00    	jmp    *0x108c6(%rip)        # 14ea0 <eventfd@GLIBC_2.7>
    45da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000045e0 <strlen@plt>:
    45e0:	f3 0f 1e fa          	endbr64
    45e4:	ff 25 be 08 01 00    	jmp    *0x108be(%rip)        # 14ea8 <strlen@Base>
    45ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000045f0 <stat@plt>:
    45f0:	f3 0f 1e fa          	endbr64
    45f4:	ff 25 b6 08 01 00    	jmp    *0x108b6(%rip)        # 14eb0 <stat@Base>
    45fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004600 <read@plt>:
    4600:	f3 0f 1e fa          	endbr64
    4604:	ff 25 ae 08 01 00    	jmp    *0x108ae(%rip)        # 14eb8 <read@Base>
    460a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004610 <__asan_handle_no_return@plt>:
    4610:	f3 0f 1e fa          	endbr64
    4614:	ff 25 a6 08 01 00    	jmp    *0x108a6(%rip)        # 14ec0 <__asan_handle_no_return@Base>
    461a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004620 <listen@plt>:
    4620:	f3 0f 1e fa          	endbr64
    4624:	ff 25 9e 08 01 00    	jmp    *0x1089e(%rip)        # 14ec8 <listen@GLIBC_2.2.5>
    462a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004630 <io_uring_register_eventfd@plt>:
    4630:	f3 0f 1e fa          	endbr64
    4634:	ff 25 96 08 01 00    	jmp    *0x10896(%rip)        # 14ed0 <io_uring_register_eventfd@LIBURING_2.0>
    463a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004640 <strtok_r@plt>:
    4640:	f3 0f 1e fa          	endbr64
    4644:	ff 25 8e 08 01 00    	jmp    *0x1088e(%rip)        # 14ed8 <strtok_r@GLIBC_2.2.5>
    464a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004650 <pthread_create@plt>:
    4650:	f3 0f 1e fa          	endbr64
    4654:	ff 25 86 08 01 00    	jmp    *0x10886(%rip)        # 14ee0 <pthread_create@Base>
    465a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004660 <io_uring_submit@plt>:
    4660:	f3 0f 1e fa          	endbr64
    4664:	ff 25 7e 08 01 00    	jmp    *0x1087e(%rip)        # 14ee8 <io_uring_submit@LIBURING_2.0>
    466a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004670 <__strcpy_chk@plt>:
    4670:	f3 0f 1e fa          	endbr64
    4674:	ff 25 76 08 01 00    	jmp    *0x10876(%rip)        # 14ef0 <__strcpy_chk@GLIBC_2.3.4>
    467a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004680 <__asan_stack_free_5@plt>:
    4680:	f3 0f 1e fa          	endbr64
    4684:	ff 25 6e 08 01 00    	jmp    *0x1086e(%rip)        # 14ef8 <__asan_stack_free_5@Base>
    468a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004690 <socket@plt>:
    4690:	f3 0f 1e fa          	endbr64
    4694:	ff 25 66 08 01 00    	jmp    *0x10866(%rip)        # 14f00 <socket@GLIBC_2.2.5>
    469a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000046a0 <memset@plt>:
    46a0:	f3 0f 1e fa          	endbr64
    46a4:	ff 25 5e 08 01 00    	jmp    *0x1085e(%rip)        # 14f08 <memset@Base>
    46aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000046b0 <__stack_chk_fail@plt>:
    46b0:	f3 0f 1e fa          	endbr64
    46b4:	ff 25 56 08 01 00    	jmp    *0x10856(%rip)        # 14f10 <__stack_chk_fail@GLIBC_2.4>
    46ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000046c0 <__asan_report_store4@plt>:
    46c0:	f3 0f 1e fa          	endbr64
    46c4:	ff 25 4e 08 01 00    	jmp    *0x1084e(%rip)        # 14f18 <__asan_report_store4@Base>
    46ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000046d0 <__asan_report_store8@plt>:
    46d0:	f3 0f 1e fa          	endbr64
    46d4:	ff 25 46 08 01 00    	jmp    *0x10846(%rip)        # 14f20 <__asan_report_store8@Base>
    46da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000046e0 <nanosleep@plt>:
    46e0:	f3 0f 1e fa          	endbr64
    46e4:	ff 25 3e 08 01 00    	jmp    *0x1083e(%rip)        # 14f28 <nanosleep@GLIBC_2.2.5>
    46ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000046f0 <__ctype_tolower_loc@plt>:
    46f0:	f3 0f 1e fa          	endbr64
    46f4:	ff 25 36 08 01 00    	jmp    *0x10836(%rip)        # 14f30 <__ctype_tolower_loc@GLIBC_2.3>
    46fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004700 <__asan_unregister_globals@plt>:
    4700:	f3 0f 1e fa          	endbr64
    4704:	ff 25 2e 08 01 00    	jmp    *0x1082e(%rip)        # 14f38 <__asan_unregister_globals@Base>
    470a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004710 <__asan_stack_free_6@plt>:
    4710:	f3 0f 1e fa          	endbr64
    4714:	ff 25 26 08 01 00    	jmp    *0x10826(%rip)        # 14f40 <__asan_stack_free_6@Base>
    471a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004720 <__sprintf_chk@plt>:
    4720:	f3 0f 1e fa          	endbr64
    4724:	ff 25 1e 08 01 00    	jmp    *0x1081e(%rip)        # 14f48 <__sprintf_chk@Base>
    472a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004730 <strcmp@plt>:
    4730:	f3 0f 1e fa          	endbr64
    4734:	ff 25 16 08 01 00    	jmp    *0x10816(%rip)        # 14f50 <strcmp@Base>
    473a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004740 <__io_uring_get_cqe@plt>:
    4740:	f3 0f 1e fa          	endbr64
    4744:	ff 25 0e 08 01 00    	jmp    *0x1080e(%rip)        # 14f58 <__io_uring_get_cqe@LIBURING_2.0>
    474a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004750 <__fprintf_chk@plt>:
    4750:	f3 0f 1e fa          	endbr64
    4754:	ff 25 06 08 01 00    	jmp    *0x10806(%rip)        # 14f60 <__fprintf_chk@Base>
    475a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004760 <__asan_register_globals@plt>:
    4760:	f3 0f 1e fa          	endbr64
    4764:	ff 25 fe 07 01 00    	jmp    *0x107fe(%rip)        # 14f68 <__asan_register_globals@Base>
    476a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004770 <__asan_stack_malloc_5@plt>:
    4770:	f3 0f 1e fa          	endbr64
    4774:	ff 25 f6 07 01 00    	jmp    *0x107f6(%rip)        # 14f70 <__asan_stack_malloc_5@Base>
    477a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004780 <bind@plt>:
    4780:	f3 0f 1e fa          	endbr64
    4784:	ff 25 ee 07 01 00    	jmp    *0x107ee(%rip)        # 14f78 <bind@GLIBC_2.2.5>
    478a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004790 <__asan_report_load1@plt>:
    4790:	f3 0f 1e fa          	endbr64
    4794:	ff 25 e6 07 01 00    	jmp    *0x107e6(%rip)        # 14f80 <__asan_report_load1@Base>
    479a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000047a0 <free@plt>:
    47a0:	f3 0f 1e fa          	endbr64
    47a4:	ff 25 de 07 01 00    	jmp    *0x107de(%rip)        # 14f88 <free@Base>
    47aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000047b0 <__asan_stack_malloc_0@plt>:
    47b0:	f3 0f 1e fa          	endbr64
    47b4:	ff 25 d6 07 01 00    	jmp    *0x107d6(%rip)        # 14f90 <__asan_stack_malloc_0@Base>
    47ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000047c0 <perror@plt>:
    47c0:	f3 0f 1e fa          	endbr64
    47c4:	ff 25 ce 07 01 00    	jmp    *0x107ce(%rip)        # 14f98 <perror@GLIBC_2.2.5>
    47ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000047d0 <__asan_report_store1@plt>:
    47d0:	f3 0f 1e fa          	endbr64
    47d4:	ff 25 c6 07 01 00    	jmp    *0x107c6(%rip)        # 14fa0 <__asan_report_store1@Base>
    47da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000047e0 <strerror@plt>:
    47e0:	f3 0f 1e fa          	endbr64
    47e4:	ff 25 be 07 01 00    	jmp    *0x107be(%rip)        # 14fa8 <strerror@Base>
    47ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000047f0 <eventfd_write@plt>:
    47f0:	f3 0f 1e fa          	endbr64
    47f4:	ff 25 b6 07 01 00    	jmp    *0x107b6(%rip)        # 14fb0 <eventfd_write@Base>
    47fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004800 <puts@plt>:
    4800:	f3 0f 1e fa          	endbr64
    4804:	ff 25 ae 07 01 00    	jmp    *0x107ae(%rip)        # 14fb8 <puts@Base>
    480a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004810 <__asan_version_mismatch_check_v8@plt>:
    4810:	f3 0f 1e fa          	endbr64
    4814:	ff 25 a6 07 01 00    	jmp    *0x107a6(%rip)        # 14fc0 <__asan_version_mismatch_check_v8@Base>
    481a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004820 <open@plt>:
    4820:	f3 0f 1e fa          	endbr64
    4824:	ff 25 9e 07 01 00    	jmp    *0x1079e(%rip)        # 14fc8 <open@GLIBC_2.2.5>
    482a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000004830 <pthread_join@plt>:
    4830:	f3 0f 1e fa          	endbr64
    4834:	ff 25 96 07 01 00    	jmp    *0x10796(%rip)        # 14fd0 <pthread_join@Base>
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
    4860:	48 8d 3d f9 cf 00 00 	lea    0xcff9(%rip),%rdi        # 11860 <_IO_stdin_used+0x860>
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
    49ef:	48 8d 3d aa d1 00 00 	lea    0xd1aa(%rip),%rdi        # 11ba0 <_IO_stdin_used+0xba0>
    49f6:	e8 45 fe ff ff       	call   4840 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    49fb:	e8 10 fc ff ff       	call   4610 <__asan_handle_no_return@plt>
    4a00:	48 8d 3d 19 d1 00 00 	lea    0xd119(%rip),%rdi        # 11b20 <_IO_stdin_used+0xb20>
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
    4a18:	48 8d 3d c1 d2 00 00 	lea    0xd2c1(%rip),%rdi        # 11ce0 <_IO_stdin_used+0xce0>
    4a1f:	e8 1c fe ff ff       	call   4840 <fatal_error>
      fatal_error("bind()");
    4a24:	e8 e7 fb ff ff       	call   4610 <__asan_handle_no_return@plt>
    4a29:	48 8d 3d 30 d1 00 00 	lea    0xd130(%rip),%rdi        # 11b60 <_IO_stdin_used+0xb60>
    4a30:	e8 0b fe ff ff       	call   4840 <fatal_error>
    4a35:	0f b6 04 25 00 80 ff 7f 	movzbl 0x7fff8000,%eax
    4a3d:	84 c0                	test   %al,%al
    4a3f:	74 02                	je     4a43 <io_thread.cold+0x71>
    4a41:	7e 1b                	jle    4a5e <io_thread.cold+0x8c>
    4a43:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    4a4b:	0f 0b                	ud2
      fatal_error("socket()");
    4a4d:	e8 be fb ff ff       	call   4610 <__asan_handle_no_return@plt>
    4a52:	48 8d 3d 87 d0 00 00 	lea    0xd087(%rip),%rdi        # 11ae0 <_IO_stdin_used+0xae0>
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
    4a74:	be 69 00 00 00       	mov    $0x69,%esi
    4a79:	48 8d 3d 40 06 01 00 	lea    0x10640(%rip),%rdi        # 150c0 <unimplemented_content+0x60>
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
    4aa5:	44 8b 0d 54 20 01 00 	mov    0x12054(%rip),%r9d        # 16b00 <__asan_option_detect_stack_use_after_return@@Base>
    4aac:	48 8d 84 24 c0 00 00 00 	lea    0xc0(%rsp),%rax
    4ab4:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
    4abc:	48 89 84 24 b0 00 00 00 	mov    %rax,0xb0(%rsp)
    4ac4:	45 85 c9             	test   %r9d,%r9d
    4ac7:	0f 85 39 2c 00 00    	jne    7706 <main+0x2c76>
    4acd:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4ad5:	48 8d 3d a4 d4 00 00 	lea    0xd4a4(%rip),%rdi        # 11f80 <_IO_stdin_used+0xf80>
    4adc:	48 8d 58 60          	lea    0x60(%rax),%rbx
    4ae0:	48 89 9c 24 b8 00 00 00 	mov    %rbx,0xb8(%rsp)
    4ae8:	48 8d 1d a5 e5 00 00 	lea    0xe5a5(%rip),%rbx        # 13094 <_IO_stdin_used+0x2094>
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
    4b4c:	48 8d 35 cd d4 00 00 	lea    0xd4cd(%rip),%rsi        # 12020 <_IO_stdin_used+0x1020>
    4b53:	31 c0                	xor    %eax,%eax
    4b55:	bf 01 00 00 00       	mov    $0x1,%edi
    4b5a:	e8 c1 f9 ff ff       	call   4520 <__printf_chk@plt>
    4b5f:	48 8d 3d fa d4 00 00 	lea    0xd4fa(%rip),%rdi        # 12060 <_IO_stdin_used+0x1060>
    4b66:	e8 95 fc ff ff       	call   4800 <puts@plt>
    4b6b:	ba 02 00 00 00       	mov    $0x2,%edx
    4b70:	48 8d 35 29 d5 00 00 	lea    0xd529(%rip),%rsi        # 120a0 <_IO_stdin_used+0x10a0>
    4b77:	31 c0                	xor    %eax,%eax
    4b79:	bf 01 00 00 00       	mov    $0x1,%edi
    4b7e:	e8 9d f9 ff ff       	call   4520 <__printf_chk@plt>
    4b83:	ba 10 00 00 00       	mov    $0x10,%edx
    4b88:	48 8d 35 51 d5 00 00 	lea    0xd551(%rip),%rsi        # 120e0 <_IO_stdin_used+0x10e0>
    4b8f:	31 c0                	xor    %eax,%eax
    4b91:	bf 01 00 00 00       	mov    $0x1,%edi
    4b96:	e8 85 f9 ff ff       	call   4520 <__printf_chk@plt>
    4b9b:	ba 01 00 00 00       	mov    $0x1,%edx
    4ba0:	48 8d 35 79 d5 00 00 	lea    0xd579(%rip),%rsi        # 12120 <_IO_stdin_used+0x1120>
    4ba7:	31 c0                	xor    %eax,%eax
    4ba9:	bf 01 00 00 00       	mov    $0x1,%edi
    4bae:	e8 6d f9 ff ff       	call   4520 <__printf_chk@plt>
    4bb3:	ba 01 00 00 00       	mov    $0x1,%edx
    4bb8:	48 8d 35 a1 d5 00 00 	lea    0xd5a1(%rip),%rsi        # 12160 <_IO_stdin_used+0x1160>
    4bbf:	31 c0                	xor    %eax,%eax
    4bc1:	bf 01 00 00 00       	mov    $0x1,%edi
    4bc6:	e8 55 f9 ff ff       	call   4520 <__printf_chk@plt>
    4bcb:	ba 02 00 00 00       	mov    $0x2,%edx
    4bd0:	48 8d 35 c9 d5 00 00 	lea    0xd5c9(%rip),%rsi        # 121a0 <_IO_stdin_used+0x11a0>
    4bd7:	31 c0                	xor    %eax,%eax
    4bd9:	bf 01 00 00 00       	mov    $0x1,%edi
    4bde:	e8 3d f9 ff ff       	call   4520 <__printf_chk@plt>
    4be3:	ba 01 00 00 00       	mov    $0x1,%edx
    4be8:	48 8d 35 f1 d5 00 00 	lea    0xd5f1(%rip),%rsi        # 121e0 <_IO_stdin_used+0x11e0>
    4bef:	31 c0                	xor    %eax,%eax
    4bf1:	bf 01 00 00 00       	mov    $0x1,%edi
    4bf6:	e8 25 f9 ff ff       	call   4520 <__printf_chk@plt>
    4bfb:	ba 01 00 00 00       	mov    $0x1,%edx
    4c00:	48 8d 35 39 d6 00 00 	lea    0xd639(%rip),%rsi        # 12240 <_IO_stdin_used+0x1240>
    4c07:	31 c0                	xor    %eax,%eax
    4c09:	bf 01 00 00 00       	mov    $0x1,%edi
    4c0e:	e8 0d f9 ff ff       	call   4520 <__printf_chk@plt>
    4c13:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    4c18:	48 8d 35 81 d6 00 00 	lea    0xd681(%rip),%rsi        # 122a0 <_IO_stdin_used+0x12a0>
    4c1f:	31 c0                	xor    %eax,%eax
    4c21:	bf 01 00 00 00       	mov    $0x1,%edi
    4c26:	e8 f5 f8 ff ff       	call   4520 <__printf_chk@plt>
    4c2b:	ba 05 00 00 00       	mov    $0x5,%edx
    4c30:	48 8d 35 a9 d6 00 00 	lea    0xd6a9(%rip),%rsi        # 122e0 <_IO_stdin_used+0x12e0>
    4c37:	31 c0                	xor    %eax,%eax
    4c39:	bf 01 00 00 00       	mov    $0x1,%edi
    4c3e:	e8 dd f8 ff ff       	call   4520 <__printf_chk@plt>
    4c43:	48 8d 3d d6 d6 00 00 	lea    0xd6d6(%rip),%rdi        # 12320 <_IO_stdin_used+0x1320>
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
    4c7f:	48 8d 35 da d6 00 00 	lea    0xd6da(%rip),%rsi        # 12360 <_IO_stdin_used+0x1360>
    4c86:	48 89 04 24          	mov    %rax,(%rsp)
    4c8a:	31 c0                	xor    %eax,%eax
    4c8c:	e8 8f f8 ff ff       	call   4520 <__printf_chk@plt>
    4c91:	ba 18 00 00 00       	mov    $0x18,%edx
    4c96:	48 8d 35 03 d7 00 00 	lea    0xd703(%rip),%rsi        # 123a0 <_IO_stdin_used+0x13a0>
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
    4cf4:	0f 8e 04 2a 00 00    	jle    76fe <main+0x2c6e>
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
    4d26:	0f 85 cd 29 00 00    	jne    76f9 <main+0x2c69>
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
    4d4b:	0f 8e 03 2a 00 00    	jle    7754 <main+0x2cc4>
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
    4d76:	0f 8e d3 29 00 00    	jle    774f <main+0x2cbf>
    4d7c:	c7 85 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rbp)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    4d86:	bf 64 00 00 00       	mov    $0x64,%edi
    4d8b:	be 20 00 00 00       	mov    $0x20,%esi
    4d90:	e8 cb f6 ff ff       	call   4460 <calloc@plt>
    4d95:	48 8d bd 88 00 00 00 	lea    0x88(%rbp),%rdi
    4d9c:	48 89 fa             	mov    %rdi,%rdx
    4d9f:	48 c1 ea 03          	shr    $0x3,%rdx
    4da3:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    4daa:	0f 85 9a 29 00 00    	jne    774a <main+0x2cba>
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
    4e38:	48 8d 35 a1 d5 00 00 	lea    0xd5a1(%rip),%rsi        # 123e0 <_IO_stdin_used+0x13e0>
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
    4ed2:	0f 85 6d 28 00 00    	jne    7745 <main+0x2cb5>
        thread_data[x].protected_state = &protected_state[k];
    4ed8:	49 8d 7a 48          	lea    0x48(%r10),%rdi
        thread_data[x].thread_index = 1;
    4edc:	45 89 42 04          	mov    %r8d,0x4(%r10)
        thread_data[x].protected_state = &protected_state[k];
    4ee0:	48 89 f9             	mov    %rdi,%rcx
    4ee3:	48 c1 e9 03          	shr    $0x3,%rcx
    4ee7:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    4eee:	0f 85 4c 28 00 00    	jne    7740 <main+0x2cb0>
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
    4f10:	0f 85 25 28 00 00    	jne    773b <main+0x2cab>
    4f16:	49 89 54 24 08       	mov    %rdx,0x8(%r12)
        my_thread_data[0] = &thread_data[other]; 
    4f1b:	4c 89 e2             	mov    %r12,%rdx
    4f1e:	48 c1 ea 03          	shr    $0x3,%rdx
    4f22:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    4f29:	0f 85 04 28 00 00    	jne    7733 <main+0x2ca3>
    4f2f:	49 89 04 24          	mov    %rax,(%r12)
    4f33:	bf 01 00 00 00       	mov    $0x1,%edi
    4f38:	89 d9                	mov    %ebx,%ecx
    4f3a:	89 ea                	mov    %ebp,%edx
    4f3c:	48 8d 35 fd d4 00 00 	lea    0xd4fd(%rip),%rsi        # 12440 <_IO_stdin_used+0x1440>
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
    4f6d:	0f 8e bb 27 00 00    	jle    772e <main+0x2c9e>
    4f73:	41 89 9a b8 00 00 00 	mov    %ebx,0xb8(%r10)
    4f7a:	8b 4c 24 50          	mov    0x50(%rsp),%ecx
    4f7e:	31 c0                	xor    %eax,%eax
    4f80:	89 ea                	mov    %ebp,%edx
    4f82:	48 8d 35 17 d5 00 00 	lea    0xd517(%rip),%rsi        # 124a0 <_IO_stdin_used+0x14a0>
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
    4fc7:	0f 85 dd 27 00 00    	jne    77aa <main+0x2d1a>
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
    4ff6:	0f 8e a6 27 00 00    	jle    77a2 <main+0x2d12>
      thread_data[x].cpu_set = sendercpu;
    4ffc:	49 8d ba b0 00 00 00 	lea    0xb0(%r10),%rdi
      thread_data[x].kind = KERNEL_THREAD;
    5003:	41 c7 02 5f 00 00 00 	movl   $0x5f,(%r10)
      thread_data[x].cpu_set = sendercpu;
    500a:	48 89 f8             	mov    %rdi,%rax
    500d:	48 c1 e8 03          	shr    $0x3,%rax
    5011:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5018:	0f 85 7f 27 00 00    	jne    779d <main+0x2d0d>
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
    503d:	0f 8e 55 27 00 00    	jle    7798 <main+0x2d08>
      thread_data[x].threads = my_thread_data;
    5043:	49 8d 7a 18          	lea    0x18(%r10),%rdi
      thread_data[x].real_thread_index = x;
    5047:	41 89 6a 08          	mov    %ebp,0x8(%r10)
      thread_data[x].threads = my_thread_data;
    504b:	48 89 f8             	mov    %rdi,%rax
    504e:	48 c1 e8 03          	shr    $0x3,%rax
    5052:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5059:	0f 85 34 27 00 00    	jne    7793 <main+0x2d03>
      thread_data[x].all_threads = thread_data;
    505f:	49 8d 7a 20          	lea    0x20(%r10),%rdi
      thread_data[x].threads = my_thread_data;
    5063:	4d 89 62 18          	mov    %r12,0x18(%r10)
      thread_data[x].all_threads = thread_data;
    5067:	48 89 f8             	mov    %rdi,%rax
    506a:	48 c1 e8 03          	shr    $0x3,%rax
    506e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5075:	0f 85 13 27 00 00    	jne    778e <main+0x2cfe>
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
    509c:	0f 8e e7 26 00 00    	jle    7789 <main+0x2cf9>
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
    50cb:	0f 85 b3 26 00 00    	jne    7784 <main+0x2cf4>
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
    50f1:	0f 8e 88 26 00 00    	jle    777f <main+0x2cef>
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
    5128:	0f 85 4c 26 00 00    	jne    777a <main+0x2cea>
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
    515b:	0f 85 14 26 00 00    	jne    7775 <main+0x2ce5>
      thread_data[x].timestamp_count = 0;
    5161:	49 8d ba 80 00 00 00 	lea    0x80(%r10),%rdi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    5168:	49 89 42 70          	mov    %rax,0x70(%r10)
      thread_data[x].timestamp_count = 0;
    516c:	48 89 f8             	mov    %rdi,%rax
    516f:	48 c1 e8 03          	shr    $0x3,%rax
    5173:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    517a:	0f 85 f0 25 00 00    	jne    7770 <main+0x2ce0>
      thread_data[x].timestamp_limit = timestamp_limit;
    5180:	49 8d ba 88 00 00 00 	lea    0x88(%r10),%rdi
      thread_data[x].timestamp_count = 0;
    5187:	49 c7 82 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%r10)
      thread_data[x].timestamp_limit = timestamp_limit;
    5192:	48 89 f8             	mov    %rdi,%rax
    5195:	48 c1 e8 03          	shr    $0x3,%rax
    5199:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    51a0:	0f 85 c5 25 00 00    	jne    776b <main+0x2cdb>
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
    51dd:	0f 85 7f 26 00 00    	jne    7862 <main+0x2dd2>
      thread_data[x].task_timestamp_count = 0;
    51e3:	49 8d ba 98 00 00 00 	lea    0x98(%r10),%rdi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    51ea:	49 89 82 90 00 00 00 	mov    %rax,0x90(%r10)
      thread_data[x].task_timestamp_count = 0;
    51f1:	48 89 f8             	mov    %rdi,%rax
    51f4:	48 c1 e8 03          	shr    $0x3,%rax
    51f8:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    51ff:	0f 85 58 26 00 00    	jne    785d <main+0x2dcd>
      thread_data[x].task_timestamp_limit = timestamp_limit;
    5205:	49 8d ba a0 00 00 00 	lea    0xa0(%r10),%rdi
      thread_data[x].task_timestamp_count = 0;
    520c:	49 c7 82 98 00 00 00 00 00 00 00 	movq   $0x0,0x98(%r10)
      thread_data[x].task_timestamp_limit = timestamp_limit;
    5217:	48 89 f8             	mov    %rdi,%rax
    521a:	48 c1 e8 03          	shr    $0x3,%rax
    521e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5225:	0f 85 2d 26 00 00    	jne    7858 <main+0x2dc8>
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
    5262:	0f 85 c9 25 00 00    	jne    7831 <main+0x2da1>
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
    52a5:	0f 85 c9 25 00 00    	jne    7874 <main+0x2de4>
    52ab:	48 8d 05 9e 28 00 00 	lea    0x289e(%rip),%rax        # 7b50 <do_protected_write>
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
    52e0:	0f 85 81 25 00 00    	jne    7867 <main+0x2dd7>
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
    5327:	48 8d 35 b2 d1 00 00 	lea    0xd1b2(%rip),%rsi        # 124e0 <_IO_stdin_used+0x14e0>
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
    537e:	0f 85 78 21 00 00    	jne    74fc <main+0x2a6c>
              mailboxes[b].higher = &data[1];
    5384:	49 8d 77 08          	lea    0x8(%r15),%rsi
              mailboxes[b].lower = &data[0];
    5388:	49 89 3f             	mov    %rdi,(%r15)
              mailboxes[b].higher = &data[1];
    538b:	48 8d 47 20          	lea    0x20(%rdi),%rax
    538f:	48 89 f2             	mov    %rsi,%rdx
    5392:	48 c1 ea 03          	shr    $0x3,%rdx
    5396:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    539d:	0f 85 61 21 00 00    	jne    7504 <main+0x2a74>
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
    53c0:	0f 8e 46 21 00 00    	jle    750c <main+0x2a7c>
              data[0].messages = messages;
    53c6:	48 89 fa             	mov    %rdi,%rdx
              mailboxes[b].kind = MAILBOX_FRIEND;
    53c9:	41 c7 47 20 01 00 00 00 	movl   $0x1,0x20(%r15)
              data[0].messages = messages;
    53d1:	48 c1 ea 03          	shr    $0x3,%rdx
    53d5:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    53dc:	0f 85 32 21 00 00    	jne    7514 <main+0x2a84>
              data[1].messages = messages2;
    53e2:	48 89 c2             	mov    %rax,%rdx
              data[0].messages = messages;
    53e5:	4c 89 37             	mov    %r14,(%rdi)
              data[1].messages = messages2;
    53e8:	48 c1 ea 03          	shr    $0x3,%rdx
    53ec:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    53f3:	0f 85 20 21 00 00    	jne    7519 <main+0x2a89>
              data[0].messages_limit = messages_limit;
    53f9:	48 8d 47 10          	lea    0x10(%rdi),%rax
              data[1].messages = messages2;
    53fd:	48 89 5f 20          	mov    %rbx,0x20(%rdi)
              data[0].messages_limit = messages_limit;
    5401:	48 89 c2             	mov    %rax,%rdx
    5404:	48 c1 ea 03          	shr    $0x3,%rdx
    5408:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    540f:	0f 85 0c 21 00 00    	jne    7521 <main+0x2a91>
              data[0].messages_count = 0;
    5415:	48 8d 47 08          	lea    0x8(%rdi),%rax
              data[0].messages_limit = messages_limit;
    5419:	48 c7 47 10 01 00 00 00 	movq   $0x1,0x10(%rdi)
              data[0].messages_count = 0;
    5421:	48 89 c2             	mov    %rax,%rdx
    5424:	48 c1 ea 03          	shr    $0x3,%rdx
    5428:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    542f:	0f 85 f4 20 00 00    	jne    7529 <main+0x2a99>
              data[1].messages_count = 0;
    5435:	48 8d 47 28          	lea    0x28(%rdi),%rax
              data[0].messages_count = 0;
    5439:	48 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%rdi)
              data[1].messages_count = 0;
    5441:	48 89 c2             	mov    %rax,%rdx
    5444:	48 c1 ea 03          	shr    $0x3,%rdx
    5448:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    544f:	0f 85 dc 20 00 00    	jne    7531 <main+0x2aa1>
              data[1].messages_limit = messages_limit;
    5455:	48 8d 47 30          	lea    0x30(%rdi),%rax
              data[1].messages_count = 0;
    5459:	48 c7 47 28 00 00 00 00 	movq   $0x0,0x28(%rdi)
              data[1].messages_limit = messages_limit;
    5461:	48 89 c2             	mov    %rax,%rdx
    5464:	48 c1 ea 03          	shr    $0x3,%rdx
    5468:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    546f:	0f 85 c4 20 00 00    	jne    7539 <main+0x2aa9>
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
    54b5:	48 8d 35 64 d0 00 00 	lea    0xd064(%rip),%rsi        # 12520 <_IO_stdin_used+0x1520>
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
    550c:	0f 85 2f 20 00 00    	jne    7541 <main+0x2ab1>
            mailboxes[b].higher = &data[1];
    5512:	48 8d 4b 08          	lea    0x8(%rbx),%rcx
            mailboxes[b].lower = &data[0];
    5516:	48 89 3b             	mov    %rdi,(%rbx)
            mailboxes[b].higher = &data[1];
    5519:	48 8d 47 20          	lea    0x20(%rdi),%rax
    551d:	48 89 ca             	mov    %rcx,%rdx
    5520:	48 c1 ea 03          	shr    $0x3,%rdx
    5524:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    552b:	0f 85 18 20 00 00    	jne    7549 <main+0x2ab9>
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
    554e:	0f 8e fd 1f 00 00    	jle    7551 <main+0x2ac1>
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
    5574:	0f 8e df 1f 00 00    	jle    7559 <main+0x2ac9>
            data[0].messages = messages;
    557a:	48 89 fa             	mov    %rdi,%rdx
            data[0].available = 0;
    557d:	c7 47 18 00 00 00 00 	movl   $0x0,0x18(%rdi)
            data[0].messages = messages;
    5584:	48 c1 ea 03          	shr    $0x3,%rdx
    5588:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    558f:	0f 85 cc 1f 00 00    	jne    7561 <main+0x2ad1>
            data[1].messages = messages2;
    5595:	48 89 c2             	mov    %rax,%rdx
            data[0].messages = messages;
    5598:	48 89 2f             	mov    %rbp,(%rdi)
            data[1].messages = messages2;
    559b:	48 c1 ea 03          	shr    $0x3,%rdx
    559f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    55a6:	0f 85 ba 1f 00 00    	jne    7566 <main+0x2ad6>
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
    55c8:	0f 8e a0 1f 00 00    	jle    756e <main+0x2ade>
            data[0].messages_limit = messages_limit;
    55ce:	48 8d 47 10          	lea    0x10(%rdi),%rax
            data[1].available = 0;
    55d2:	c7 47 38 00 00 00 00 	movl   $0x0,0x38(%rdi)
            data[0].messages_limit = messages_limit;
    55d9:	48 89 c2             	mov    %rax,%rdx
    55dc:	48 c1 ea 03          	shr    $0x3,%rdx
    55e0:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    55e7:	0f 85 89 1f 00 00    	jne    7576 <main+0x2ae6>
            data[0].messages_count = 0;
    55ed:	48 8d 47 08          	lea    0x8(%rdi),%rax
            data[0].messages_limit = messages_limit;
    55f1:	48 c7 47 10 01 00 00 00 	movq   $0x1,0x10(%rdi)
            data[0].messages_count = 0;
    55f9:	48 89 c2             	mov    %rax,%rdx
    55fc:	48 c1 ea 03          	shr    $0x3,%rdx
    5600:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    5607:	0f 85 71 1f 00 00    	jne    757e <main+0x2aee>
            data[1].messages_count = 0;
    560d:	48 8d 47 28          	lea    0x28(%rdi),%rax
            data[0].messages_count = 0;
    5611:	48 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%rdi)
            data[1].messages_count = 0;
    5619:	48 89 c2             	mov    %rax,%rdx
    561c:	48 c1 ea 03          	shr    $0x3,%rdx
    5620:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    5627:	0f 85 59 1f 00 00    	jne    7586 <main+0x2af6>
            data[1].messages_limit = messages_limit;
    562d:	48 8d 47 30          	lea    0x30(%rdi),%rax
            data[1].messages_count = 0;
    5631:	48 c7 47 28 00 00 00 00 	movq   $0x0,0x28(%rdi)
            data[1].messages_limit = messages_limit;
    5639:	48 89 c2             	mov    %rax,%rdx
    563c:	48 c1 ea 03          	shr    $0x3,%rdx
    5640:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    5647:	0f 85 41 1f 00 00    	jne    758e <main+0x2afe>
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
    569b:	48 8d 0d be ce 00 00 	lea    0xcebe(%rip),%rcx        # 12560 <_IO_stdin_used+0x1560>
    56a2:	31 c0                	xor    %eax,%eax
    56a4:	48 89 df             	mov    %rbx,%rdi
    56a7:	be 01 00 00 00       	mov    $0x1,%esi
    56ac:	e8 6f f0 ff ff       	call   4720 <__sprintf_chk@plt>
          messaged->message = message;
    56b1:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    56b6:	4c 89 d8             	mov    %r11,%rax
    56b9:	48 c1 e8 03          	shr    $0x3,%rax
    56bd:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    56c4:	0f 85 a2 21 00 00    	jne    786c <main+0x2ddc>
          messaged->task_index = y;
    56ca:	49 8d 7b 10          	lea    0x10(%r11),%rdi
          messaged->message = message;
    56ce:	49 89 1b             	mov    %rbx,(%r11)
          messaged->task_index = y;
    56d1:	48 89 f8             	mov    %rdi,%rax
    56d4:	48 c1 e8 03          	shr    $0x3,%rax
    56d8:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    56df:	0f 85 6f 1f 00 00    	jne    7654 <main+0x2bc4>
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
    5710:	0f 85 36 1f 00 00    	jne    764c <main+0x2bbc>
    5716:	48 8b 04 24          	mov    (%rsp),%rax
    571a:	49 8d 7b 08          	lea    0x8(%r11),%rdi
    571e:	48 89 fa             	mov    %rdi,%rdx
    5721:	48 63 40 04          	movslq 0x4(%rax),%rax
    5725:	48 c1 ea 03          	shr    $0x3,%rdx
    5729:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    5730:	49 89 c7             	mov    %rax,%r15
    5733:	0f 85 0e 1f 00 00    	jne    7647 <main+0x2bb7>
    5739:	49 89 43 08          	mov    %rax,0x8(%r11)
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    573d:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5742:	48 c1 e8 03          	shr    $0x3,%rax
    5746:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    574d:	0f 85 ea 1e 00 00    	jne    763d <main+0x2bad>
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
    5777:	0f 8e b8 1e 00 00    	jle    7635 <main+0x2ba5>
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
    57a7:	0f 8e 83 1e 00 00    	jle    7630 <main+0x2ba0>
          thread_data[x].tasks[y].message = messaged;
    57ad:	48 8d bb 88 01 00 00 	lea    0x188(%rbx),%rdi
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    57b4:	89 83 90 01 00 00    	mov    %eax,0x190(%rbx)
          thread_data[x].tasks[y].message = messaged;
    57ba:	48 89 f8             	mov    %rdi,%rax
    57bd:	48 c1 e8 03          	shr    $0x3,%rax
    57c1:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    57c8:	0f 85 5d 1e 00 00    	jne    762b <main+0x2b9b>
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
    57f0:	0f 8e 30 1e 00 00    	jle    7626 <main+0x2b96>
          thread_data[x].tasks[y].snapshot_count = 99;
    57f6:	48 8d bb 58 01 00 00 	lea    0x158(%rbx),%rdi
          thread_data[x].tasks[y].sending = 1;
    57fd:	c7 83 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rbx)
          thread_data[x].tasks[y].snapshot_count = 99;
    5807:	48 89 f8             	mov    %rdi,%rax
    580a:	48 c1 e8 03          	shr    $0x3,%rax
    580e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5815:	0f 85 98 1e 00 00    	jne    76b3 <main+0x2c23>
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
    5854:	0f 85 54 1e 00 00    	jne    76ae <main+0x2c1e>
          thread_data[x].tasks[y].current_snapshot = 0;
    585a:	48 8d bb 60 01 00 00 	lea    0x160(%rbx),%rdi
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    5861:	48 89 83 50 01 00 00 	mov    %rax,0x150(%rbx)
          thread_data[x].tasks[y].current_snapshot = 0;
    5868:	48 89 f8             	mov    %rdi,%rax
    586b:	48 c1 e8 03          	shr    $0x3,%rax
    586f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5876:	0f 85 2d 1e 00 00    	jne    76a9 <main+0x2c19>
    587c:	48 c7 83 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    5887:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    588c:	48 c1 e8 03          	shr    $0x3,%rax
    5890:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5897:	0f 85 02 1e 00 00    	jne    769f <main+0x2c0f>
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
    58c8:	0f 85 cc 1d 00 00    	jne    769a <main+0x2c0a>
    58ce:	48 8d bb 30 01 00 00 	lea    0x130(%rbx),%rdi
    58d5:	8b 70 04             	mov    0x4(%rax),%esi
    58d8:	48 89 f9             	mov    %rdi,%rcx
    58db:	48 c1 e9 03          	shr    $0x3,%rcx
    58df:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    58e6:	84 c9                	test   %cl,%cl
    58e8:	74 09                	je     58f3 <main+0xe63>
    58ea:	80 f9 03             	cmp    $0x3,%cl
    58ed:	0f 8e a2 1d 00 00    	jle    7695 <main+0x2c05>
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    58f3:	48 8d bb 28 01 00 00 	lea    0x128(%rbx),%rdi
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    58fa:	89 b3 30 01 00 00    	mov    %esi,0x130(%rbx)
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    5900:	48 89 f9             	mov    %rdi,%rcx
    5903:	48 c1 e9 03          	shr    $0x3,%rcx
    5907:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    590e:	0f 85 7c 1d 00 00    	jne    7690 <main+0x2c00>
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    5914:	48 8b 34 24          	mov    (%rsp),%rsi
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    5918:	48 89 83 28 01 00 00 	mov    %rax,0x128(%rbx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    591f:	48 39 f0             	cmp    %rsi,%rax
    5922:	0f 85 59 1d 00 00    	jne    7681 <main+0x2bf1>
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
    594c:	0f 85 2a 1d 00 00    	jne    767c <main+0x2bec>
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
    5977:	0f 8e fa 1c 00 00    	jle    7677 <main+0x2be7>
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
    59ab:	0f 85 c1 1c 00 00    	jne    7672 <main+0x2be2>
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
    59d6:	0f 8e 91 1c 00 00    	jle    766d <main+0x2bdd>
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
    5a0a:	0f 85 58 1c 00 00    	jne    7668 <main+0x2bd8>
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
    5a35:	0f 8e 28 1c 00 00    	jle    7663 <main+0x2bd3>
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
    5a60:	0f 8e f8 1b 00 00    	jle    765e <main+0x2bce>
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
    5a94:	0f 85 bf 1b 00 00    	jne    7659 <main+0x2bc9>
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
    5ac5:	0f 85 19 1b 00 00    	jne    75e4 <main+0x2b54>
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
    5b01:	0f 85 d8 1a 00 00    	jne    75df <main+0x2b4f>
    5b07:	48 8d 05 a2 8e 00 00 	lea    0x8ea2(%rip),%rax        # e9b0 <barriered_work>
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
    5b39:	0f 85 9b 1a 00 00    	jne    75da <main+0x2b4a>
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
    5b76:	0f 85 56 1a 00 00    	jne    75d2 <main+0x2b42>
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    5b7c:	48 89 f8             	mov    %rdi,%rax
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    5b7f:	49 89 7a 50          	mov    %rdi,0x50(%r10)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    5b83:	48 c1 e8 03          	shr    $0x3,%rax
    5b87:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5b8e:	0f 85 39 1a 00 00    	jne    75cd <main+0x2b3d>
    5b94:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    5b99:	48 89 07             	mov    %rax,(%rdi)
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
    5b9c:	49 8d bf 20 05 00 00 	lea    0x520(%r15),%rdi
    5ba3:	48 89 f8             	mov    %rdi,%rax
    5ba6:	48 c1 e8 03          	shr    $0x3,%rax
    5baa:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5bb1:	0f 85 11 1a 00 00    	jne    75c8 <main+0x2b38>
    5bb7:	48 8d 05 92 1f 00 00 	lea    0x1f92(%rip),%rax        # 7b50 <do_protected_write>
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    5bbe:	49 8d bf 18 05 00 00 	lea    0x518(%r15),%rdi
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
    5bc5:	49 89 87 20 05 00 00 	mov    %rax,0x520(%r15)
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    5bcc:	48 89 f8             	mov    %rdi,%rax
    5bcf:	48 c1 e8 03          	shr    $0x3,%rax
    5bd3:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5bda:	0f 85 e3 19 00 00    	jne    75c3 <main+0x2b33>
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    5be0:	49 8d bf 28 05 00 00 	lea    0x528(%r15),%rdi
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    5be7:	48 8d 05 42 20 00 00 	lea    0x2042(%rip),%rax        # 7c30 <barriered_reset>
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    5bee:	48 89 fa             	mov    %rdi,%rdx
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    5bf1:	49 89 87 18 05 00 00 	mov    %rax,0x518(%r15)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    5bf8:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5bfd:	48 c1 ea 03          	shr    $0x3,%rdx
    5c01:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    5c08:	48 8b 00             	mov    (%rax),%rax
    5c0b:	0f 85 ad 19 00 00    	jne    75be <main+0x2b2e>
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
    5c3c:	0f 85 77 19 00 00    	jne    75b9 <main+0x2b29>
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
    5c68:	0f 8e 46 19 00 00    	jle    75b4 <main+0x2b24>
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
    5c9d:	0f 85 0c 19 00 00    	jne    75af <main+0x2b1f>
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
    5cd2:	0f 85 d2 18 00 00    	jne    75aa <main+0x2b1a>
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
    5cfe:	0f 8e a1 18 00 00    	jle    75a5 <main+0x2b15>
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
    5d2f:	0f 85 f7 1a 00 00    	jne    782c <main+0x2d9c>
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
    5d5b:	0f 8e c6 1a 00 00    	jle    7827 <main+0x2d97>
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
    5d90:	48 8d 0d 49 95 00 00 	lea    0x9549(%rip),%rcx        # f2e0 <barriered_work_ingest_andwork>
    5d97:	41 bc 01 00 00 00    	mov    $0x1,%r12d
            thread_data[x].tasks[y].run = barriered_work; 
    5d9d:	48 8d bb 18 01 00 00 	lea    0x118(%rbx),%rdi
    5da4:	48 89 f8             	mov    %rdi,%rax
    5da7:	48 c1 e8 03          	shr    $0x3,%rax
    5dab:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5db2:	0f 85 6a 1a 00 00    	jne    7822 <main+0x2d92>
    5db8:	48 89 8b 18 01 00 00 	mov    %rcx,0x118(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    5dbf:	e9 b7 f4 ff ff       	jmp    527b <main+0x7eb>
    5dc4:	48 8d 0d e5 8b 00 00 	lea    0x8be5(%rip),%rcx        # e9b0 <barriered_work>
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
    5e28:	0f 85 22 1a 00 00    	jne    7850 <main+0x2dc0>
    5e2e:	49 81 0f ff 0f 00 00 	orq    $0xfff,(%r15)
          for (int j = 0 ; j < cores ; j++) {
    5e35:	e9 a8 f1 ff ff       	jmp    4fe2 <main+0x552>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5e3a:	4c 8b 5c 24 48       	mov    0x48(%rsp),%r11
    5e3f:	ba 0d 00 00 00       	mov    $0xd,%edx
    5e44:	48 8d 35 75 c7 00 00 	lea    0xc775(%rip),%rsi        # 125c0 <_IO_stdin_used+0x15c0>
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
    5e78:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    5e7d:	48 89 f8             	mov    %rdi,%rax
    5e80:	48 c1 e8 03          	shr    $0x3,%rax
    5e84:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5e8b:	0f 85 ba 19 00 00    	jne    784b <main+0x2dbb>
    5e91:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5e96:	48 89 07             	mov    %rax,(%rdi)
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    5e99:	48 8d 47 08          	lea    0x8(%rdi),%rax
    5e9d:	48 89 c2             	mov    %rax,%rdx
    5ea0:	48 c1 ea 03          	shr    $0x3,%rdx
    5ea4:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    5eab:	0f 85 92 19 00 00    	jne    7843 <main+0x2db3>
    thread_data[x].threads = my_thread_data;
    5eb1:	49 8d 83 d8 09 00 00 	lea    0x9d8(%r11),%rax
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    5eb8:	4c 89 5f 08          	mov    %r11,0x8(%rdi)
    thread_data[x].threads = my_thread_data;
    5ebc:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    5ec1:	48 c1 e8 03          	shr    $0x3,%rax
    5ec5:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5ecc:	0f 85 67 19 00 00    	jne    7839 <main+0x2da9>
    thread_data[x].thread_count = 2;
    5ed2:	49 8d 83 e8 09 00 00 	lea    0x9e8(%r11),%rax
    thread_data[x].threads = my_thread_data;
    5ed9:	49 89 bb d8 09 00 00 	mov    %rdi,0x9d8(%r11)
    thread_data[x].thread_count = 2;
    5ee0:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    5ee5:	48 c1 e8 03          	shr    $0x3,%rax
    5ee9:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    5ef0:	84 c0                	test   %al,%al
    5ef2:	74 08                	je     5efc <main+0x146c>
    5ef4:	3c 03                	cmp    $0x3,%al
    5ef6:	0f 8e 9f 16 00 00    	jle    759b <main+0x2b0b>
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
    5f2b:	0f 85 f1 1a 00 00    	jne    7a22 <main+0x2f92>
    thread_data[x].task_count = total_barrier_count;
    5f31:	49 8d 83 00 0a 00 00 	lea    0xa00(%r11),%rax
    thread_data[x].thread_index = 0;
    5f38:	41 c7 83 c4 09 00 00 00 00 00 00 	movl   $0x0,0x9c4(%r11)
    thread_data[x].task_count = total_barrier_count;
    5f43:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    5f48:	48 c1 e8 03          	shr    $0x3,%rax
    5f4c:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    5f53:	84 c0                	test   %al,%al
    5f55:	74 08                	je     5f5f <main+0x14cf>
    5f57:	3c 03                	cmp    $0x3,%al
    5f59:	0f 8e b9 1a 00 00    	jle    7a18 <main+0x2f88>
    5f5f:	41 c7 83 00 0a 00 00 03 00 00 00 	movl   $0x3,0xa00(%r11)
    thread_data[n].tasks[0].scheduled = 1;
    5f6a:	49 8d 43 38          	lea    0x38(%r11),%rax
    5f6e:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    5f73:	48 c1 e8 03          	shr    $0x3,%rax
    5f77:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5f7e:	0f 85 d5 19 00 00    	jne    7959 <main+0x2ec9>
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
    5fac:	0f 85 d6 18 00 00    	jne    7888 <main+0x2df8>
    5fb2:	49 8d 83 c0 00 00 00 	lea    0xc0(%r11),%rax
    5fb9:	49 8d bb f8 00 00 00 	lea    0xf8(%r11),%rdi
    5fc0:	c7 82 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rdx)
    5fca:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    5fcf:	48 89 f8             	mov    %rdi,%rax
    5fd2:	48 c1 e8 03          	shr    $0x3,%rax
    5fd6:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    5fdd:	0f 85 dd 16 00 00    	jne    76c0 <main+0x2c30>
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
    600e:	0f 85 6f 18 00 00    	jne    7883 <main+0x2df3>
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
    60a8:	0f 85 d0 17 00 00    	jne    787e <main+0x2dee>
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
    60dd:	0f 85 96 17 00 00    	jne    7879 <main+0x2de9>
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
    6109:	0f 8e 04 19 00 00    	jle    7a13 <main+0x2f83>
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
    613f:	0f 85 dc 14 00 00    	jne    7621 <main+0x2b91>
    6145:	48 8d 47 08          	lea    0x8(%rdi),%rax
    6149:	4c 89 1f             	mov    %r11,(%rdi)
    614c:	48 89 c2             	mov    %rax,%rdx
    614f:	48 c1 ea 03          	shr    $0x3,%rdx
    6153:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    615a:	0f 85 b9 14 00 00    	jne    7619 <main+0x2b89>
    6160:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    6165:	49 8d 93 80 01 00 00 	lea    0x180(%r11),%rdx
    616c:	48 89 47 08          	mov    %rax,0x8(%rdi)
    6170:	48 8d 47 10          	lea    0x10(%rdi),%rax
    6174:	48 89 c1             	mov    %rax,%rcx
    6177:	48 c1 e9 03          	shr    $0x3,%rcx
    617b:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    6182:	0f 85 92 16 00 00    	jne    781a <main+0x2d8a>
    6188:	48 8d 47 18          	lea    0x18(%rdi),%rax
    618c:	48 89 57 10          	mov    %rdx,0x10(%rdi)
    6190:	49 8d 93 40 02 00 00 	lea    0x240(%r11),%rdx
    6197:	48 89 c1             	mov    %rax,%rcx
    619a:	48 c1 e9 03          	shr    $0x3,%rcx
    619e:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    61a5:	0f 85 67 16 00 00    	jne    7812 <main+0x2d82>
    61ab:	48 8d 47 20          	lea    0x20(%rdi),%rax
    61af:	48 89 57 18          	mov    %rdx,0x18(%rdi)
    61b3:	49 8d 93 00 03 00 00 	lea    0x300(%r11),%rdx
    61ba:	48 89 c1             	mov    %rax,%rcx
    61bd:	48 c1 e9 03          	shr    $0x3,%rcx
    61c1:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    61c8:	0f 85 3c 16 00 00    	jne    780a <main+0x2d7a>
    61ce:	48 8d 47 28          	lea    0x28(%rdi),%rax
    61d2:	48 89 57 20          	mov    %rdx,0x20(%rdi)
    61d6:	49 8d 93 c0 03 00 00 	lea    0x3c0(%r11),%rdx
    61dd:	48 89 c1             	mov    %rax,%rcx
    61e0:	48 c1 e9 03          	shr    $0x3,%rcx
    61e4:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    61eb:	0f 85 11 16 00 00    	jne    7802 <main+0x2d72>
    61f1:	48 8d 47 30          	lea    0x30(%rdi),%rax
    61f5:	48 89 57 28          	mov    %rdx,0x28(%rdi)
    61f9:	49 8d 93 80 04 00 00 	lea    0x480(%r11),%rdx
    6200:	48 89 c1             	mov    %rax,%rcx
    6203:	48 c1 e9 03          	shr    $0x3,%rcx
    6207:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    620e:	0f 85 e6 15 00 00    	jne    77fa <main+0x2d6a>
    6214:	48 8d 47 38          	lea    0x38(%rdi),%rax
    6218:	48 89 57 30          	mov    %rdx,0x30(%rdi)
    621c:	49 8d 93 40 05 00 00 	lea    0x540(%r11),%rdx
    6223:	48 89 c1             	mov    %rax,%rcx
    6226:	48 c1 e9 03          	shr    $0x3,%rcx
    622a:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    6231:	0f 85 bb 15 00 00    	jne    77f2 <main+0x2d62>
    6237:	48 8d 47 40          	lea    0x40(%rdi),%rax
    623b:	48 89 57 38          	mov    %rdx,0x38(%rdi)
    623f:	49 8d 93 00 06 00 00 	lea    0x600(%r11),%rdx
    6246:	48 89 c1             	mov    %rax,%rcx
    6249:	48 c1 e9 03          	shr    $0x3,%rcx
    624d:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    6254:	0f 85 90 15 00 00    	jne    77ea <main+0x2d5a>
    625a:	48 8d 47 48          	lea    0x48(%rdi),%rax
    625e:	48 89 57 40          	mov    %rdx,0x40(%rdi)
    6262:	49 8d 93 c0 06 00 00 	lea    0x6c0(%r11),%rdx
    6269:	48 89 c1             	mov    %rax,%rcx
    626c:	48 c1 e9 03          	shr    $0x3,%rcx
    6270:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    6277:	0f 85 65 15 00 00    	jne    77e2 <main+0x2d52>
    627d:	48 8d 47 50          	lea    0x50(%rdi),%rax
    6281:	48 89 57 48          	mov    %rdx,0x48(%rdi)
    6285:	49 8d 93 80 07 00 00 	lea    0x780(%r11),%rdx
    628c:	48 89 c1             	mov    %rax,%rcx
    628f:	48 c1 e9 03          	shr    $0x3,%rcx
    6293:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    629a:	0f 85 61 13 00 00    	jne    7601 <main+0x2b71>
    62a0:	48 8d 47 58          	lea    0x58(%rdi),%rax
    62a4:	48 89 57 50          	mov    %rdx,0x50(%rdi)
    62a8:	49 8d 93 40 08 00 00 	lea    0x840(%r11),%rdx
    62af:	48 89 c1             	mov    %rax,%rcx
    62b2:	48 c1 e9 03          	shr    $0x3,%rcx
    62b6:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    62bd:	0f 85 36 13 00 00    	jne    75f9 <main+0x2b69>
    62c3:	48 8d 47 60          	lea    0x60(%rdi),%rax
    62c7:	48 89 57 58          	mov    %rdx,0x58(%rdi)
    62cb:	4d 8d ab 00 09 00 00 	lea    0x900(%r11),%r13
    62d2:	48 89 c2             	mov    %rax,%rdx
    62d5:	48 c1 ea 03          	shr    $0x3,%rdx
    62d9:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    62e0:	0f 85 0b 13 00 00    	jne    75f1 <main+0x2b61>
    62e6:	48 8d 47 68          	lea    0x68(%rdi),%rax
    62ea:	4c 89 6f 60          	mov    %r13,0x60(%rdi)
    62ee:	48 89 c2             	mov    %rax,%rdx
    62f1:	48 c1 ea 03          	shr    $0x3,%rdx
    62f5:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    62fc:	0f 85 e7 12 00 00    	jne    75e9 <main+0x2b59>
    6302:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6307:	49 8d 93 80 0a 00 00 	lea    0xa80(%r11),%rdx
    630e:	48 89 47 68          	mov    %rax,0x68(%rdi)
    6312:	48 8d 47 70          	lea    0x70(%rdi),%rax
    6316:	48 89 c1             	mov    %rax,%rcx
    6319:	48 c1 e9 03          	shr    $0x3,%rcx
    631d:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    6324:	0f 85 e7 12 00 00    	jne    7611 <main+0x2b81>
    632a:	48 8d 47 78          	lea    0x78(%rdi),%rax
    632e:	48 89 57 70          	mov    %rdx,0x70(%rdi)
    6332:	49 8d 93 40 0b 00 00 	lea    0xb40(%r11),%rdx
    6339:	48 89 c1             	mov    %rax,%rcx
    633c:	48 c1 e9 03          	shr    $0x3,%rcx
    6340:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    6347:	0f 85 bc 12 00 00    	jne    7609 <main+0x2b79>
  thread_data[timer_threadi].threads = my_thread_data;
    634d:	49 8d 83 18 09 00 00 	lea    0x918(%r11),%rax
    my_thread_data[n] = &thread_data[n]; 
    6354:	48 89 57 78          	mov    %rdx,0x78(%rdi)
  thread_data[timer_threadi].threads = my_thread_data;
    6358:	48 89 c2             	mov    %rax,%rdx
    635b:	48 c1 ea 03          	shr    $0x3,%rdx
    635f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    6366:	0f 85 4c 13 00 00    	jne    76b8 <main+0x2c28>
    636c:	49 89 bb 18 09 00 00 	mov    %rdi,0x918(%r11)
  thread_data[timer_threadi].total_thread_count = total_threads;
    6373:	49 8d bb 2c 09 00 00 	lea    0x92c(%r11),%rdi
    637a:	48 89 f8             	mov    %rdi,%rax
    637d:	48 c1 e8 03          	shr    $0x3,%rax
    6381:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    6388:	48 89 f8             	mov    %rdi,%rax
    638b:	83 e0 07             	and    $0x7,%eax
    638e:	83 c0 03             	add    $0x3,%eax
    6391:	38 d0                	cmp    %dl,%al
    6393:	7c 08                	jl     639d <main+0x190d>
    6395:	84 d2                	test   %dl,%dl
    6397:	0f 85 71 16 00 00    	jne    7a0e <main+0x2f7e>
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    639d:	49 8d bb 28 09 00 00 	lea    0x928(%r11),%rdi
  thread_data[timer_threadi].total_thread_count = total_threads;
    63a4:	41 c7 83 2c 09 00 00 10 00 00 00 	movl   $0x10,0x92c(%r11)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    63af:	48 89 f8             	mov    %rdi,%rax
    63b2:	48 c1 e8 03          	shr    $0x3,%rax
    63b6:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    63bd:	84 c0                	test   %al,%al
    63bf:	74 08                	je     63c9 <main+0x1939>
    63c1:	3c 03                	cmp    $0x3,%al
    63c3:	0f 8e 40 16 00 00    	jle    7a09 <main+0x2f79>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    63c9:	49 8d bb 30 09 00 00 	lea    0x930(%r11),%rdi
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    63d0:	41 c7 83 28 09 00 00 0c 00 00 00 	movl   $0xc,0x928(%r11)
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    63db:	48 89 f8             	mov    %rdi,%rax
    63de:	48 c1 e8 03          	shr    $0x3,%rax
    63e2:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    63e9:	84 c0                	test   %al,%al
    63eb:	74 08                	je     63f5 <main+0x1965>
    63ed:	3c 03                	cmp    $0x3,%al
    63ef:	0f 8e 0f 16 00 00    	jle    7a04 <main+0x2f74>
  thread_data[timer_threadi].thread_index = 0;
    63f5:	49 8d bb 04 09 00 00 	lea    0x904(%r11),%rdi
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    63fc:	41 c7 83 30 09 00 00 0c 00 00 00 	movl   $0xc,0x930(%r11)
  thread_data[timer_threadi].thread_index = 0;
    6407:	48 89 f8             	mov    %rdi,%rax
    640a:	48 c1 e8 03          	shr    $0x3,%rax
    640e:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    6415:	48 89 f8             	mov    %rdi,%rax
    6418:	83 e0 07             	and    $0x7,%eax
    641b:	83 c0 03             	add    $0x3,%eax
    641e:	38 d0                	cmp    %dl,%al
    6420:	7c 08                	jl     642a <main+0x199a>
    6422:	84 d2                	test   %dl,%dl
    6424:	0f 85 d5 15 00 00    	jne    79ff <main+0x2f6f>
    642a:	ba 0c 00 00 00       	mov    $0xc,%edx
    642f:	48 8d 35 ca c1 00 00 	lea    0xc1ca(%rip),%rsi        # 12600 <_IO_stdin_used+0x1600>
    6436:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    6438:	31 ed                	xor    %ebp,%ebp
  thread_data[timer_threadi].thread_index = 0;
    643a:	41 c7 83 04 09 00 00 00 00 00 00 	movl   $0x0,0x904(%r11)
    6445:	bf 01 00 00 00       	mov    $0x1,%edi
    644a:	4c 89 1c 24          	mov    %r11,(%rsp)
    644e:	e8 cd e0 ff ff       	call   4520 <__printf_chk@plt>
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    6453:	4c 89 e9             	mov    %r13,%rcx
    6456:	48 8d 7b 60          	lea    0x60(%rbx),%rdi
    645a:	41 89 ed             	mov    %ebp,%r13d
    645d:	48 8d 15 3c 1d 00 00 	lea    0x1d3c(%rip),%rdx        # 81a0 <timer_thread>
    6464:	49 8d b4 24 a0 02 00 00 	lea    0x2a0(%r12),%rsi
    646c:	e8 df e1 ff ff       	call   4650 <pthread_create@plt>
    6471:	4c 8b 1c 24          	mov    (%rsp),%r11
    6475:	4d 89 f0             	mov    %r14,%r8
    6478:	48 89 d9             	mov    %rbx,%rcx
    647b:	4c 89 7c 24 60       	mov    %r15,0x60(%rsp)
    6480:	41 be 02 00 00 00    	mov    $0x2,%r14d
    6486:	4c 89 5c 24 58       	mov    %r11,0x58(%rsp)
    648b:	4c 89 da             	mov    %r11,%rdx
    648e:	48 89 5c 24 68       	mov    %rbx,0x68(%rsp)
    6493:	48 89 5c 24 70       	mov    %rbx,0x70(%rsp)
    for (int d = 0 ; d < threads_per_group ; d++) {
    6498:	48 89 14 24          	mov    %rdx,(%rsp)
    649c:	47 8d 7c 2d 00       	lea    0x0(%r13,%r13,1),%r15d
  int curcpu = 0;
    64a1:	4c 89 c5             	mov    %r8,%rbp
    64a4:	49 89 cc             	mov    %rcx,%r12
    64a7:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    64ac:	48 89 d3             	mov    %rdx,%rbx
    64af:	4c 89 44 24 10       	mov    %r8,0x10(%rsp)
      thread_data[x].type = WORKER;
    64b4:	48 8d 7b 0c          	lea    0xc(%rbx),%rdi
    64b8:	48 89 f8             	mov    %rdi,%rax
    64bb:	48 c1 e8 03          	shr    $0x3,%rax
    64bf:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    64c6:	48 89 f8             	mov    %rdi,%rax
    64c9:	83 e0 07             	and    $0x7,%eax
    64cc:	83 c0 03             	add    $0x3,%eax
    64cf:	38 d0                	cmp    %dl,%al
    64d1:	7c 08                	jl     64db <main+0x1a4b>
    64d3:	84 d2                	test   %dl,%dl
    64d5:	0f 85 e6 12 00 00    	jne    77c1 <main+0x2d31>
      thread_data[x].running = 1;
    64db:	48 8d 7b 44          	lea    0x44(%rbx),%rdi
      thread_data[x].type = WORKER;
    64df:	c7 43 0c 01 00 00 00 	movl   $0x1,0xc(%rbx)
      thread_data[x].running = 1;
    64e6:	48 89 f8             	mov    %rdi,%rax
    64e9:	48 c1 e8 03          	shr    $0x3,%rax
    64ed:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    64f4:	48 89 f8             	mov    %rdi,%rax
    64f7:	83 e0 07             	and    $0x7,%eax
    64fa:	83 c0 03             	add    $0x3,%eax
    64fd:	38 d0                	cmp    %dl,%al
    64ff:	7c 08                	jl     6509 <main+0x1a79>
    6501:	84 d2                	test   %dl,%dl
    6503:	0f 85 ab 12 00 00    	jne    77b4 <main+0x2d24>
    6509:	c7 43 44 01 00 00 00 	movl   $0x1,0x44(%rbx)
    6510:	44 89 e9             	mov    %r13d,%ecx
    6513:	44 89 fa             	mov    %r15d,%edx
    6516:	31 c0                	xor    %eax,%eax
    6518:	48 8d 35 21 c1 00 00 	lea    0xc121(%rip),%rsi        # 12640 <_IO_stdin_used+0x1640>
    651f:	bf 01 00 00 00       	mov    $0x1,%edi
    6524:	e8 f7 df ff ff       	call   4520 <__printf_chk@plt>
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    6529:	4c 89 e7             	mov    %r12,%rdi
    652c:	48 89 d9             	mov    %rbx,%rcx
    652f:	48 89 ee             	mov    %rbp,%rsi
    6532:	48 8d 15 47 75 00 00 	lea    0x7547(%rip),%rdx        # da80 <barriered_thread>
    6539:	e8 12 e1 ff ff       	call   4650 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    653e:	48 8d bb b0 00 00 00 	lea    0xb0(%rbx),%rdi
    6545:	48 89 f8             	mov    %rdi,%rax
    6548:	48 c1 e8 03          	shr    $0x3,%rax
    654c:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6553:	0f 85 56 12 00 00    	jne    77af <main+0x2d1f>
    6559:	4c 89 e0             	mov    %r12,%rax
    655c:	48 8b 93 b0 00 00 00 	mov    0xb0(%rbx),%rdx
    6563:	48 c1 e8 03          	shr    $0x3,%rax
    6567:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    656e:	0f 85 45 12 00 00    	jne    77b9 <main+0x2d29>
    6574:	49 8b 3c 24          	mov    (%r12),%rdi
    for (int d = 0 ; d < threads_per_group ; d++) {
    6578:	41 83 c7 01          	add    $0x1,%r15d
    657c:	49 83 c4 08          	add    $0x8,%r12
    6580:	48 83 c5 38          	add    $0x38,%rbp
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    6584:	be 08 00 00 00       	mov    $0x8,%esi
    for (int d = 0 ; d < threads_per_group ; d++) {
    6589:	48 81 c3 c0 00 00 00 	add    $0xc0,%rbx
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    6590:	e8 ab de ff ff       	call   4440 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    6595:	45 39 f7             	cmp    %r14d,%r15d
    6598:	0f 85 16 ff ff ff    	jne    64b4 <main+0x1a24>
  for (int k = 0 ; k < group_count ; k++) {
    659e:	48 8b 14 24          	mov    (%rsp),%rdx
    65a2:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    65a7:	41 83 c5 01          	add    $0x1,%r13d
    65ab:	45 8d 77 02          	lea    0x2(%r15),%r14d
    65af:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    65b4:	48 81 c2 80 01 00 00 	add    $0x180,%rdx
    65bb:	48 83 c1 10          	add    $0x10,%rcx
    65bf:	49 83 c0 70          	add    $0x70,%r8
    65c3:	41 83 fd 06          	cmp    $0x6,%r13d
    65c7:	0f 85 cb fe ff ff    	jne    6498 <main+0x1a08>
    thread_data[x].type = IO;
    65cd:	4c 8b 5c 24 58       	mov    0x58(%rsp),%r11
    65d2:	4c 8b 7c 24 60       	mov    0x60(%rsp),%r15
    65d7:	4c 8b 6c 24 68       	mov    0x68(%rsp),%r13
    65dc:	48 8b 5c 24 70       	mov    0x70(%rsp),%rbx
    65e1:	49 8d bb cc 09 00 00 	lea    0x9cc(%r11),%rdi
    65e8:	48 89 f8             	mov    %rdi,%rax
    65eb:	48 c1 e8 03          	shr    $0x3,%rax
    65ef:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    65f6:	48 89 f8             	mov    %rdi,%rax
    65f9:	83 e0 07             	and    $0x7,%eax
    65fc:	83 c0 03             	add    $0x3,%eax
    65ff:	38 d0                	cmp    %dl,%al
    6601:	7c 08                	jl     660b <main+0x1b7b>
    6603:	84 d2                	test   %dl,%dl
    6605:	0f 85 ef 13 00 00    	jne    79fa <main+0x2f6a>
    thread_data[x].running = 1;
    660b:	49 8d bb 04 0a 00 00 	lea    0xa04(%r11),%rdi
    thread_data[x].type = IO;
    6612:	41 c7 83 cc 09 00 00 02 00 00 00 	movl   $0x2,0x9cc(%r11)
    thread_data[x].running = 1;
    661d:	48 89 f8             	mov    %rdi,%rax
    6620:	48 c1 e8 03          	shr    $0x3,%rax
    6624:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    662b:	48 89 f8             	mov    %rdi,%rax
    662e:	83 e0 07             	and    $0x7,%eax
    6631:	83 c0 03             	add    $0x3,%eax
    6634:	38 d0                	cmp    %dl,%al
    6636:	7c 08                	jl     6640 <main+0x1bb0>
    6638:	84 d2                	test   %dl,%dl
    663a:	0f 85 b5 13 00 00    	jne    79f5 <main+0x2f65>
    6640:	41 c7 83 04 0a 00 00 01 00 00 00 	movl   $0x1,0xa04(%r11)
    thread_data[x].task_count = 0;
    664b:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    6650:	48 c1 e8 03          	shr    $0x3,%rax
    6654:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    665b:	84 c0                	test   %al,%al
    665d:	74 08                	je     6667 <main+0x1bd7>
    665f:	3c 03                	cmp    $0x3,%al
    6661:	0f 8e 84 13 00 00    	jle    79eb <main+0x2f5b>
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    6667:	bf 01 00 00 00       	mov    $0x1,%edi
    666c:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].task_count = 0;
    6671:	4c 89 1c 24          	mov    %r11,(%rsp)
    6675:	41 c7 83 00 0a 00 00 00 00 00 00 	movl   $0x0,0xa00(%r11)
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    6680:	e8 db dd ff ff       	call   4460 <calloc@plt>
    6685:	4c 8b 1c 24          	mov    (%rsp),%r11
    6689:	49 8d bb 18 0a 00 00 	lea    0xa18(%r11),%rdi
    6690:	48 89 fa             	mov    %rdi,%rdx
    6693:	48 c1 ea 03          	shr    $0x3,%rdx
    6697:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    669e:	0f 85 39 11 00 00    	jne    77dd <main+0x2d4d>
    66a4:	49 89 83 18 0a 00 00 	mov    %rax,0xa18(%r11)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    66ab:	31 ff                	xor    %edi,%edi
    66ad:	be 00 08 00 00       	mov    $0x800,%esi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    66b2:	4c 89 1c 24          	mov    %r11,(%rsp)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    66b6:	e8 15 df ff ff       	call   45d0 <eventfd@plt>
    66bb:	4c 8b 1c 24          	mov    (%rsp),%r11
    66bf:	49 8d bb 20 0a 00 00 	lea    0xa20(%r11),%rdi
    66c6:	48 89 fa             	mov    %rdi,%rdx
    66c9:	48 c1 ea 03          	shr    $0x3,%rdx
    66cd:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    66d4:	84 d2                	test   %dl,%dl
    66d6:	74 09                	je     66e1 <main+0x1c51>
    66d8:	80 fa 03             	cmp    $0x3,%dl
    66db:	0f 8e 0e 12 00 00    	jle    78ef <main+0x2e5f>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    66e1:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    66e6:	41 89 83 20 0a 00 00 	mov    %eax,0xa20(%r11)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    66ed:	be 08 00 00 00       	mov    $0x8,%esi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    66f2:	4c 89 1c 24          	mov    %r11,(%rsp)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    66f6:	e8 65 dd ff ff       	call   4460 <calloc@plt>
      my_thread_data[n] = &thread_data[n]; 
    66fb:	4c 8b 1c 24          	mov    (%rsp),%r11
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    66ff:	48 89 c7             	mov    %rax,%rdi
      my_thread_data[n] = &thread_data[n]; 
    6702:	48 c1 e8 03          	shr    $0x3,%rax
    6706:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    670d:	0f 85 bb 10 00 00    	jne    77ce <main+0x2d3e>
    6713:	48 8d 47 08          	lea    0x8(%rdi),%rax
    6717:	4c 89 1f             	mov    %r11,(%rdi)
    671a:	48 89 c2             	mov    %rax,%rdx
    671d:	48 c1 ea 03          	shr    $0x3,%rdx
    6721:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    6728:	0f 85 98 10 00 00    	jne    77c6 <main+0x2d36>
    672e:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    6733:	48 89 47 08          	mov    %rax,0x8(%rdi)
    thread_data[x].threads = my_thread_data;
    6737:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    673c:	48 c1 e8 03          	shr    $0x3,%rax
    6740:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6747:	0f 85 86 10 00 00    	jne    77d3 <main+0x2d43>
    thread_data[x].thread_count = thread_count;
    674d:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    thread_data[x].threads = my_thread_data;
    6752:	49 89 bb d8 09 00 00 	mov    %rdi,0x9d8(%r11)
    thread_data[x].thread_count = thread_count;
    6759:	48 c1 e8 03          	shr    $0x3,%rax
    675d:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    6764:	84 c0                	test   %al,%al
    6766:	74 08                	je     6770 <main+0x1ce0>
    6768:	3c 03                	cmp    $0x3,%al
    676a:	0f 8e 75 11 00 00    	jle    78e5 <main+0x2e55>
    6770:	41 c7 83 e8 09 00 00 02 00 00 00 	movl   $0x2,0x9e8(%r11)
    thread_data[x].thread_index = x;
    677b:	4c 89 f8             	mov    %r15,%rax
    677e:	48 c1 e8 03          	shr    $0x3,%rax
    6782:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    6789:	4c 89 f8             	mov    %r15,%rax
    678c:	83 e0 07             	and    $0x7,%eax
    678f:	83 c0 03             	add    $0x3,%eax
    6792:	38 d0                	cmp    %dl,%al
    6794:	7c 08                	jl     679e <main+0x1d0e>
    6796:	84 d2                	test   %dl,%dl
    6798:	0f 85 3f 11 00 00    	jne    78dd <main+0x2e4d>
    679e:	ba 0d 00 00 00       	mov    $0xd,%edx
    67a3:	bf 01 00 00 00       	mov    $0x1,%edi
    67a8:	31 c0                	xor    %eax,%eax
    67aa:	4c 89 1c 24          	mov    %r11,(%rsp)
    67ae:	41 c7 83 c4 09 00 00 0d 00 00 00 	movl   $0xd,0x9c4(%r11)
    67b9:	48 8d 35 e0 be 00 00 	lea    0xbee0(%rip),%rsi        # 126a0 <_IO_stdin_used+0x16a0>
    67c0:	4c 8d 73 70          	lea    0x70(%rbx),%r14
    67c4:	e8 57 dd ff ff       	call   4520 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    67c9:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
    67ce:	48 8d 7b 68          	lea    0x68(%rbx),%rdi
    67d2:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    67d7:	48 8d 15 82 55 00 00 	lea    0x5582(%rip),%rdx        # bd60 <io_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    67de:	bb 0e 00 00 00       	mov    $0xe,%ebx
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    67e3:	48 81 c6 d8 02 00 00 	add    $0x2d8,%rsi
    67ea:	e8 61 de ff ff       	call   4650 <pthread_create@plt>
    67ef:	ba 0e 00 00 00       	mov    $0xe,%edx
    67f4:	48 8d 35 e5 be 00 00 	lea    0xbee5(%rip),%rsi        # 126e0 <_IO_stdin_used+0x16e0>
    67fb:	31 c0                	xor    %eax,%eax
    67fd:	bf 01 00 00 00       	mov    $0x1,%edi
    6802:	e8 19 dd ff ff       	call   4520 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    6807:	4c 8b 1c 24          	mov    (%rsp),%r11
    680b:	4c 8b 7c 24 50       	mov    0x50(%rsp),%r15
    6810:	4d 8d a3 8c 0a 00 00 	lea    0xa8c(%r11),%r12
    6817:	49 81 c7 10 03 00 00 	add    $0x310,%r15
    681e:	4c 89 e5             	mov    %r12,%rbp
    6821:	4d 89 dc             	mov    %r11,%r12
    6824:	89 da                	mov    %ebx,%edx
    6826:	48 8d 35 f3 be 00 00 	lea    0xbef3(%rip),%rsi        # 12720 <_IO_stdin_used+0x1720>
    682d:	bf 01 00 00 00       	mov    $0x1,%edi
    6832:	31 c0                	xor    %eax,%eax
    6834:	e8 e7 dc ff ff       	call   4520 <__printf_chk@plt>
    thread_data[x].type = EXTERNAL;
    6839:	48 8d 45 f4          	lea    -0xc(%rbp),%rax
    683d:	48 89 04 24          	mov    %rax,(%rsp)
    6841:	48 89 e8             	mov    %rbp,%rax
    6844:	48 c1 e8 03          	shr    $0x3,%rax
    6848:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    684f:	48 89 e8             	mov    %rbp,%rax
    6852:	83 e0 07             	and    $0x7,%eax
    6855:	83 c0 03             	add    $0x3,%eax
    6858:	38 d0                	cmp    %dl,%al
    685a:	7c 08                	jl     6864 <main+0x1dd4>
    685c:	84 d2                	test   %dl,%dl
    685e:	0f 85 71 10 00 00    	jne    78d5 <main+0x2e45>
    thread_data[x].running = 1;
    6864:	48 8d 7d 38          	lea    0x38(%rbp),%rdi
    thread_data[x].type = EXTERNAL;
    6868:	c7 45 00 03 00 00 00 	movl   $0x3,0x0(%rbp)
    thread_data[x].running = 1;
    686f:	48 89 f8             	mov    %rdi,%rax
    6872:	48 c1 e8 03          	shr    $0x3,%rax
    6876:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    687d:	48 89 f8             	mov    %rdi,%rax
    6880:	83 e0 07             	and    $0x7,%eax
    6883:	83 c0 03             	add    $0x3,%eax
    6886:	38 d0                	cmp    %dl,%al
    6888:	7c 08                	jl     6892 <main+0x1e02>
    688a:	84 d2                	test   %dl,%dl
    688c:	0f 85 3e 10 00 00    	jne    78d0 <main+0x2e40>
    thread_data[x].task_count = 0;
    6892:	48 8d 7d 34          	lea    0x34(%rbp),%rdi
    thread_data[x].running = 1;
    6896:	c7 45 38 01 00 00 00 	movl   $0x1,0x38(%rbp)
    thread_data[x].task_count = 0;
    689d:	48 89 f8             	mov    %rdi,%rax
    68a0:	48 c1 e8 03          	shr    $0x3,%rax
    68a4:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    68ab:	84 c0                	test   %al,%al
    68ad:	74 08                	je     68b7 <main+0x1e27>
    68af:	3c 03                	cmp    $0x3,%al
    68b1:	0f 8e 14 10 00 00    	jle    78cb <main+0x2e3b>
    68b7:	c7 45 34 00 00 00 00 	movl   $0x0,0x34(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    68be:	bf 01 00 00 00       	mov    $0x1,%edi
    68c3:	be 08 00 00 00       	mov    $0x8,%esi
    68c8:	e8 93 db ff ff       	call   4460 <calloc@plt>
    68cd:	48 89 c7             	mov    %rax,%rdi
    68d0:	48 8d 45 44          	lea    0x44(%rbp),%rax
    68d4:	48 89 c2             	mov    %rax,%rdx
    68d7:	48 c1 ea 03          	shr    $0x3,%rdx
    68db:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    68e2:	0f 85 db 0f 00 00    	jne    78c3 <main+0x2e33>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    68e8:	48 89 f8             	mov    %rdi,%rax
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    68eb:	48 89 7d 44          	mov    %rdi,0x44(%rbp)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    68ef:	48 c1 e8 03          	shr    $0x3,%rax
    68f3:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    68fa:	0f 85 be 0f 00 00    	jne    78be <main+0x2e2e>
    6900:	48 8b 84 24 a0 00 00 00 	mov    0xa0(%rsp),%rax
    6908:	48 89 07             	mov    %rax,(%rdi)
	  thread_data[x].buffers_count = 1;
    690b:	48 8d bd b0 00 00 00 	lea    0xb0(%rbp),%rdi
    6912:	48 89 f8             	mov    %rdi,%rax
    6915:	48 c1 e8 03          	shr    $0x3,%rax
    6919:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    6920:	48 89 f8             	mov    %rdi,%rax
    6923:	83 e0 07             	and    $0x7,%eax
    6926:	83 c0 03             	add    $0x3,%eax
    6929:	38 d0                	cmp    %dl,%al
    692b:	7c 08                	jl     6935 <main+0x1ea5>
    692d:	84 d2                	test   %dl,%dl
    692f:	0f 85 84 0f 00 00    	jne    78b9 <main+0x2e29>
    6935:	c7 85 b0 00 00 00 01 00 00 00 	movl   $0x1,0xb0(%rbp)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    693f:	bf 02 00 00 00       	mov    $0x2,%edi
    6944:	be 08 00 00 00       	mov    $0x8,%esi
    6949:	e8 12 db ff ff       	call   4460 <calloc@plt>
    694e:	48 89 c7             	mov    %rax,%rdi
      my_thread_data[n] = &thread_data[n]; 
    6951:	48 c1 e8 03          	shr    $0x3,%rax
    6955:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    695c:	0f 85 52 0f 00 00    	jne    78b4 <main+0x2e24>
    6962:	48 8d 47 08          	lea    0x8(%rdi),%rax
    6966:	4c 89 27             	mov    %r12,(%rdi)
    6969:	48 89 c2             	mov    %rax,%rdx
    696c:	48 c1 ea 03          	shr    $0x3,%rdx
    6970:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    6977:	0f 85 2f 0f 00 00    	jne    78ac <main+0x2e1c>
    697d:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    6982:	48 89 47 08          	mov    %rax,0x8(%rdi)
    thread_data[x].threads = my_thread_data;
    6986:	48 8d 45 0c          	lea    0xc(%rbp),%rax
    698a:	48 89 c2             	mov    %rax,%rdx
    698d:	48 c1 ea 03          	shr    $0x3,%rdx
    6991:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    6998:	0f 85 06 0f 00 00    	jne    78a4 <main+0x2e14>
    699e:	48 89 7d 0c          	mov    %rdi,0xc(%rbp)
    thread_data[x].thread_count = thread_count;
    69a2:	48 8d 7d 1c          	lea    0x1c(%rbp),%rdi
    69a6:	48 89 f8             	mov    %rdi,%rax
    69a9:	48 c1 e8 03          	shr    $0x3,%rax
    69ad:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    69b4:	84 c0                	test   %al,%al
    69b6:	74 08                	je     69c0 <main+0x1f30>
    69b8:	3c 03                	cmp    $0x3,%al
    69ba:	0f 8e df 0e 00 00    	jle    789f <main+0x2e0f>
    thread_data[x].total_thread_count = total_threads;
    69c0:	48 8d 7d 20          	lea    0x20(%rbp),%rdi
    thread_data[x].thread_count = thread_count;
    69c4:	c7 45 1c 02 00 00 00 	movl   $0x2,0x1c(%rbp)
    thread_data[x].total_thread_count = total_threads;
    69cb:	48 89 f8             	mov    %rdi,%rax
    69ce:	48 c1 e8 03          	shr    $0x3,%rax
    69d2:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    69d9:	48 89 f8             	mov    %rdi,%rax
    69dc:	83 e0 07             	and    $0x7,%eax
    69df:	83 c0 03             	add    $0x3,%eax
    69e2:	38 d0                	cmp    %dl,%al
    69e4:	7c 08                	jl     69ee <main+0x1f5e>
    69e6:	84 d2                	test   %dl,%dl
    69e8:	0f 85 ac 0e 00 00    	jne    789a <main+0x2e0a>
    thread_data[x].thread_index = x;
    69ee:	48 8d 7d f8          	lea    -0x8(%rbp),%rdi
    thread_data[x].total_thread_count = total_threads;
    69f2:	c7 45 20 10 00 00 00 	movl   $0x10,0x20(%rbp)
    thread_data[x].thread_index = x;
    69f9:	48 89 f8             	mov    %rdi,%rax
    69fc:	48 c1 e8 03          	shr    $0x3,%rax
    6a00:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    6a07:	48 89 f8             	mov    %rdi,%rax
    6a0a:	83 e0 07             	and    $0x7,%eax
    6a0d:	83 c0 03             	add    $0x3,%eax
    6a10:	38 d0                	cmp    %dl,%al
    6a12:	7c 08                	jl     6a1c <main+0x1f8c>
    6a14:	84 d2                	test   %dl,%dl
    6a16:	0f 85 79 0e 00 00    	jne    7895 <main+0x2e05>
    6a1c:	89 5d f8             	mov    %ebx,-0x8(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    6a1f:	48 8b 0c 24          	mov    (%rsp),%rcx
    6a23:	4c 89 fe             	mov    %r15,%rsi
    6a26:	4c 89 f7             	mov    %r14,%rdi
    6a29:	48 8d 15 e0 13 00 00 	lea    0x13e0(%rip),%rdx        # 7e10 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    6a30:	48 81 c5 c0 00 00 00 	add    $0xc0,%rbp
    6a37:	49 83 c6 08          	add    $0x8,%r14
    6a3b:	49 83 c7 38          	add    $0x38,%r15
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    6a3f:	e8 0c dc ff ff       	call   4650 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    6a44:	48 83 84 24 a0 00 00 00 10 	addq   $0x10,0xa0(%rsp)
    6a4d:	83 fb 0e             	cmp    $0xe,%ebx
    6a50:	75 0a                	jne    6a5c <main+0x1fcc>
    6a52:	bb 0f 00 00 00       	mov    $0xf,%ebx
    6a57:	e9 c8 fd ff ff       	jmp    6824 <main+0x1d94>
    6a5c:	4d 89 e3             	mov    %r12,%r11
    6a5f:	4d 8d 74 24 08       	lea    0x8(%r12),%r14
    6a64:	48 8d 1d f5 bc 00 00 	lea    0xbcf5(%rip),%rbx        # 12760 <_IO_stdin_used+0x1760>
    6a6b:	4d 8d a4 24 08 0c 00 00 	lea    0xc08(%r12),%r12
    6a73:	4c 89 dd             	mov    %r11,%rbp
    6a76:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
    6a80:	4c 89 f0             	mov    %r14,%rax
    6a83:	48 c1 e8 03          	shr    $0x3,%rax
    6a87:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    6a8e:	84 c0                	test   %al,%al
    6a90:	74 08                	je     6a9a <main+0x200a>
    6a92:	3c 03                	cmp    $0x3,%al
    6a94:	0f 8e f3 0d 00 00    	jle    788d <main+0x2dfd>
    6a9a:	49 8d 7e fc          	lea    -0x4(%r14),%rdi
    6a9e:	41 8b 0e             	mov    (%r14),%ecx
    6aa1:	48 89 f8             	mov    %rdi,%rax
    6aa4:	48 c1 e8 03          	shr    $0x3,%rax
    6aa8:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    6aaf:	48 89 f8             	mov    %rdi,%rax
    6ab2:	83 e0 07             	and    $0x7,%eax
    6ab5:	83 c0 03             	add    $0x3,%eax
    6ab8:	38 d0                	cmp    %dl,%al
    6aba:	7c 08                	jl     6ac4 <main+0x2034>
    6abc:	84 d2                	test   %dl,%dl
    6abe:	0f 85 22 0f 00 00    	jne    79e6 <main+0x2f56>
    6ac4:	41 8b 56 fc          	mov    -0x4(%r14),%edx
    6ac8:	48 89 de             	mov    %rbx,%rsi
    6acb:	bf 01 00 00 00       	mov    $0x1,%edi
    6ad0:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    6ad2:	49 81 c6 c0 00 00 00 	add    $0xc0,%r14
    6ad9:	e8 42 da ff ff       	call   4520 <__printf_chk@plt>
    6ade:	4d 39 e6             	cmp    %r12,%r14
    6ae1:	75 9d                	jne    6a80 <main+0x1ff0>
    6ae3:	48 8d 3d b6 bc 00 00 	lea    0xbcb6(%rip),%rdi        # 127a0 <_IO_stdin_used+0x17a0>
    6aea:	48 89 2c 24          	mov    %rbp,(%rsp)
  for (int x = 0 ; x < total_threads ; x++) {
    6aee:	31 db                	xor    %ebx,%ebx
    6af0:	4c 8d 25 e9 bc 00 00 	lea    0xbce9(%rip),%r12        # 127e0 <_IO_stdin_used+0x17e0>
    6af7:	e8 04 dd ff ff       	call   4800 <puts@plt>
    6afc:	48 8b 84 24 b8 00 00 00 	mov    0xb8(%rsp),%rax
    6b04:	4c 8b 34 24          	mov    (%rsp),%r14
    6b08:	4c 8d 78 c0          	lea    -0x40(%rax),%r15
    6b0c:	0f 1f 40 00          	nopl   0x0(%rax)
    void * result; 
    6b10:	4c 89 fd             	mov    %r15,%rbp
    pthread_join(thread[x], &result);
    6b13:	4c 89 e8             	mov    %r13,%rax
    void * result; 
    6b16:	48 c1 ed 03          	shr    $0x3,%rbp
    pthread_join(thread[x], &result);
    6b1a:	48 c1 e8 03          	shr    $0x3,%rax
    void * result; 
    6b1e:	c6 85 00 80 ff 7f 00 	movb   $0x0,0x7fff8000(%rbp)
    pthread_join(thread[x], &result);
    6b25:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6b2c:	0f 85 ac 0e 00 00    	jne    79de <main+0x2f4e>
    6b32:	49 8b 7d 00          	mov    0x0(%r13),%rdi
    6b36:	4c 89 fe             	mov    %r15,%rsi
  for (int x = 0 ; x < total_threads ; x++) {
    6b39:	49 83 c5 08          	add    $0x8,%r13
    pthread_join(thread[x], &result);
    6b3d:	e8 ee dc ff ff       	call   4830 <pthread_join@plt>
    6b42:	89 da                	mov    %ebx,%edx
    6b44:	4c 89 e6             	mov    %r12,%rsi
    6b47:	bf 01 00 00 00       	mov    $0x1,%edi
    6b4c:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    6b4e:	83 c3 01             	add    $0x1,%ebx
    6b51:	e8 ca d9 ff ff       	call   4520 <__printf_chk@plt>
    6b56:	c6 85 00 80 ff 7f f8 	movb   $0xf8,0x7fff8000(%rbp)
    6b5d:	83 fb 10             	cmp    $0x10,%ebx
    6b60:	75 ae                	jne    6b10 <main+0x2080>
  long received = 0;
    6b62:	45 31 d2             	xor    %r10d,%r10d
  long ingests = 0;
    6b65:	45 31 c0             	xor    %r8d,%r8d
    6b68:	48 8b 6c 24 40       	mov    0x40(%rsp),%rbp
    6b6d:	4c 89 74 24 30       	mov    %r14,0x30(%rsp)
  for (int x = 0 ; x < thread_count ; x++) {
    6b72:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
  long total = 0;
    6b7a:	45 31 ff             	xor    %r15d,%r15d
    6b7d:	4d 89 d4             	mov    %r10,%r12
    6b80:	4d 89 c6             	mov    %r8,%r14
  long sents = 0;
    6b83:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
  long sends = 0;
    6b8c:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
    6b95:	bf 0a 00 00 00       	mov    $0xa,%edi
    6b9a:	8b 5c 24 28          	mov    0x28(%rsp),%ebx
    6b9e:	e8 8d d9 ff ff       	call   4530 <putchar@plt>
    printf("Total Protected %ld\n", protected_state[me].protected);
    6ba3:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    6bab:	83 f3 01             	xor    $0x1,%ebx
    6bae:	48 c1 e8 03          	shr    $0x3,%rax
    6bb2:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6bb9:	0f 85 12 0e 00 00    	jne    79d1 <main+0x2f41>
    6bbf:	48 8d 35 5a bc 00 00 	lea    0xbc5a(%rip),%rsi        # 12820 <_IO_stdin_used+0x1820>
    6bc6:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    6bce:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    6bd3:	4c 8d 6d 08          	lea    0x8(%rbp),%r13
    6bd7:	48 8b 10             	mov    (%rax),%rdx
    6bda:	31 c0                	xor    %eax,%eax
    6bdc:	e8 3f d9 ff ff       	call   4520 <__printf_chk@plt>
    6be1:	4c 89 e8             	mov    %r13,%rax
    6be4:	48 c1 e8 03          	shr    $0x3,%rax
    6be8:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    6bef:	84 c0                	test   %al,%al
    6bf1:	74 08                	je     6bfb <main+0x216b>
    6bf3:	3c 03                	cmp    $0x3,%al
    6bf5:	0f 8e 68 0d 00 00    	jle    7963 <main+0x2ed3>
    6bfb:	8b 45 08             	mov    0x8(%rbp),%eax
    6bfe:	85 c0                	test   %eax,%eax
    6c00:	0f 8e ea 08 00 00    	jle    74f0 <main+0x2a60>
      v += thread_data[me].tasks[n].v;
    6c06:	48 89 ea             	mov    %rbp,%rdx
    6c09:	48 c1 ea 03          	shr    $0x3,%rdx
    6c0d:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    6c14:	0f 85 56 0d 00 00    	jne    7970 <main+0x2ee0>
    6c1a:	48 8b 75 00          	mov    0x0(%rbp),%rsi
    6c1e:	48 63 c8             	movslq %eax,%rcx
    long v = 0;
    6c21:	31 d2                	xor    %edx,%edx
    6c23:	48 c1 e1 09          	shl    $0x9,%rcx
    6c27:	48 8d be 10 01 00 00 	lea    0x110(%rsi),%rdi
    6c2e:	48 01 f9             	add    %rdi,%rcx
    6c31:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      v += thread_data[me].tasks[n].v;
    6c38:	48 89 f8             	mov    %rdi,%rax
    6c3b:	48 c1 e8 03          	shr    $0x3,%rax
    6c3f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6c46:	0f 85 1f 0d 00 00    	jne    796b <main+0x2edb>
    6c4c:	48 03 17             	add    (%rdi),%rdx
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    6c4f:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    6c56:	48 39 f9             	cmp    %rdi,%rcx
    6c59:	75 dd                	jne    6c38 <main+0x21a8>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    6c5b:	48 63 cb             	movslq %ebx,%rcx
    6c5e:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    6c63:	48 f7 d9             	neg    %rcx
    6c66:	81 e1 c0 00 00 00    	and    $0xc0,%ecx
    6c6c:	48 01 c1             	add    %rax,%rcx
    6c6f:	48 8d 79 40          	lea    0x40(%rcx),%rdi
    6c73:	48 89 f8             	mov    %rdi,%rax
    6c76:	48 c1 e8 03          	shr    $0x3,%rax
    6c7a:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    6c81:	84 c0                	test   %al,%al
    6c83:	74 08                	je     6c8d <main+0x21fd>
    6c85:	3c 03                	cmp    $0x3,%al
    6c87:	0f 8e 02 0d 00 00    	jle    798f <main+0x2eff>
    6c8d:	8b 41 40             	mov    0x40(%rcx),%eax
    6c90:	85 c0                	test   %eax,%eax
    6c92:	7e 57                	jle    6ceb <main+0x225b>
      v += thread_data[other].tasks[n].v;
    6c94:	48 8d 79 38          	lea    0x38(%rcx),%rdi
    6c98:	48 89 fe             	mov    %rdi,%rsi
    6c9b:	48 c1 ee 03          	shr    $0x3,%rsi
    6c9f:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    6ca6:	0f 85 de 0c 00 00    	jne    798a <main+0x2efa>
    6cac:	48 8b 79 38          	mov    0x38(%rcx),%rdi
    6cb0:	48 63 c8             	movslq %eax,%rcx
    6cb3:	48 c1 e1 09          	shl    $0x9,%rcx
    6cb7:	48 81 c7 10 01 00 00 	add    $0x110,%rdi
    6cbe:	48 01 f9             	add    %rdi,%rcx
    6cc1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6cc8:	48 89 f8             	mov    %rdi,%rax
    6ccb:	48 c1 e8 03          	shr    $0x3,%rax
    6ccf:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6cd6:	0f 85 a9 0c 00 00    	jne    7985 <main+0x2ef5>
    6cdc:	48 03 17             	add    (%rdi),%rdx
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    6cdf:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    6ce6:	48 39 f9             	cmp    %rdi,%rcx
    6ce9:	75 dd                	jne    6cc8 <main+0x2238>
    6ceb:	31 c0                	xor    %eax,%eax
    6ced:	48 8d 35 6c bb 00 00 	lea    0xbb6c(%rip),%rsi        # 12860 <_IO_stdin_used+0x1860>
    6cf4:	bf 01 00 00 00       	mov    $0x1,%edi
    6cf9:	e8 22 d8 ff ff       	call   4520 <__printf_chk@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    6cfe:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    6d06:	48 c1 e8 03          	shr    $0x3,%rax
    6d0a:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6d11:	0f 85 61 0c 00 00    	jne    7978 <main+0x2ee8>
    6d17:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    6d1f:	48 8d 35 7a bb 00 00 	lea    0xbb7a(%rip),%rsi        # 128a0 <_IO_stdin_used+0x18a0>
    6d26:	bf 01 00 00 00       	mov    $0x1,%edi
    6d2b:	48 8b 08             	mov    (%rax),%rcx
    6d2e:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    6d38:	48 f7 e9             	imul   %rcx
    6d3b:	48 c1 f9 3f          	sar    $0x3f,%rcx
    6d3f:	31 c0                	xor    %eax,%eax
    6d41:	48 d1 fa             	sar    %rdx
    6d44:	48 29 ca             	sub    %rcx,%rdx
    6d47:	e8 d4 d7 ff ff       	call   4520 <__printf_chk@plt>
    6d4c:	bf 0a 00 00 00       	mov    $0xa,%edi
    6d51:	e8 da d7 ff ff       	call   4530 <putchar@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    6d56:	4c 89 e8             	mov    %r13,%rax
    6d59:	48 c1 e8 03          	shr    $0x3,%rax
    6d5d:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    6d64:	84 c0                	test   %al,%al
    6d66:	74 08                	je     6d70 <main+0x22e0>
    6d68:	3c 03                	cmp    $0x3,%al
    6d6a:	0f 8e 59 0c 00 00    	jle    79c9 <main+0x2f39>
    6d70:	8b 45 08             	mov    0x8(%rbp),%eax
    6d73:	85 c0                	test   %eax,%eax
    6d75:	0f 8e 2a 01 00 00    	jle    6ea5 <main+0x2415>
      total += thread_data[x].tasks[n].n;
    6d7b:	48 89 ea             	mov    %rbp,%rdx
    6d7e:	48 c1 ea 03          	shr    $0x3,%rdx
    6d82:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    6d89:	0f 85 32 0c 00 00    	jne    79c1 <main+0x2f31>
    6d8f:	48 8b 5d 00          	mov    0x0(%rbp),%rbx
    6d93:	48 63 c8             	movslq %eax,%rcx
    6d96:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    6d9b:	48 c1 e1 09          	shl    $0x9,%rcx
    6d9f:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6da4:	48 8d bb 08 01 00 00 	lea    0x108(%rbx),%rdi
    6dab:	48 01 f9             	add    %rdi,%rcx
    6dae:	66 90                	xchg   %ax,%ax
    6db0:	48 89 f8             	mov    %rdi,%rax
    6db3:	48 c1 e8 03          	shr    $0x3,%rax
    6db7:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6dbe:	0f 85 f8 0b 00 00    	jne    79bc <main+0x2f2c>
      ingests += thread_data[x].tasks[n].ingest_count;
    6dc4:	48 8d 47 60          	lea    0x60(%rdi),%rax
      total += thread_data[x].tasks[n].n;
    6dc8:	4c 03 3f             	add    (%rdi),%r15
      ingests += thread_data[x].tasks[n].ingest_count;
    6dcb:	48 89 c2             	mov    %rax,%rdx
    6dce:	48 c1 ea 03          	shr    $0x3,%rdx
    6dd2:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    6dd9:	0f 85 d5 0b 00 00    	jne    79b4 <main+0x2f24>
      sends += thread_data[x].tasks[n].sends;
    6ddf:	48 8d 47 70          	lea    0x70(%rdi),%rax
      ingests += thread_data[x].tasks[n].ingest_count;
    6de3:	4c 03 77 60          	add    0x60(%rdi),%r14
      sends += thread_data[x].tasks[n].sends;
    6de7:	48 89 c2             	mov    %rax,%rdx
    6dea:	48 c1 ea 03          	shr    $0x3,%rdx
    6dee:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    6df5:	0f 85 b1 0b 00 00    	jne    79ac <main+0x2f1c>
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    6dfb:	48 8d 47 68          	lea    0x68(%rdi),%rax
      sends += thread_data[x].tasks[n].sends;
    6dff:	4c 03 57 70          	add    0x70(%rdi),%r10
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    6e03:	48 89 c2             	mov    %rax,%rdx
    6e06:	48 c1 ea 03          	shr    $0x3,%rdx
    6e0a:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    6e11:	0f 85 8d 0b 00 00    	jne    79a4 <main+0x2f14>
    6e17:	48 8b 47 68          	mov    0x68(%rdi),%rax
    6e1b:	48 8d 50 10          	lea    0x10(%rax),%rdx
    6e1f:	48 89 d6             	mov    %rdx,%rsi
    6e22:	48 c1 ee 03          	shr    $0x3,%rsi
    6e26:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    6e2d:	0f 85 69 0b 00 00    	jne    799c <main+0x2f0c>
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    6e33:	48 8d 50 18          	lea    0x18(%rax),%rdx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    6e37:	4c 03 58 10          	add    0x10(%rax),%r11
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    6e3b:	48 89 d6             	mov    %rdx,%rsi
    6e3e:	48 c1 ee 03          	shr    $0x3,%rsi
    6e42:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    6e49:	0f 85 45 0b 00 00    	jne    7994 <main+0x2f04>
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    6e4f:	48 8d 50 38          	lea    0x38(%rax),%rdx
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    6e53:	4c 03 60 18          	add    0x18(%rax),%r12
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    6e57:	48 89 d6             	mov    %rdx,%rsi
    6e5a:	48 c1 ee 03          	shr    $0x3,%rsi
    6e5e:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    6e65:	0f 85 e6 0a 00 00    	jne    7951 <main+0x2ec1>
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    6e6b:	48 8d 50 40          	lea    0x40(%rax),%rdx
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    6e6f:	4c 03 58 38          	add    0x38(%rax),%r11
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    6e73:	48 89 d6             	mov    %rdx,%rsi
    6e76:	48 c1 ee 03          	shr    $0x3,%rsi
    6e7a:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    6e81:	0f 85 c2 0a 00 00    	jne    7949 <main+0x2eb9>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    6e87:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    6e8e:	4c 03 60 40          	add    0x40(%rax),%r12
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    6e92:	48 39 f9             	cmp    %rdi,%rcx
    6e95:	0f 85 15 ff ff ff    	jne    6db0 <main+0x2320>
    6e9b:	4c 89 5c 24 18       	mov    %r11,0x18(%rsp)
    6ea0:	4c 89 54 24 20       	mov    %r10,0x20(%rsp)
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    6ea5:	48 8d 7d 50          	lea    0x50(%rbp),%rdi
    6ea9:	48 89 f8             	mov    %rdi,%rax
    6eac:	48 c1 e8 03          	shr    $0x3,%rax
    6eb0:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6eb7:	0f 85 87 0a 00 00    	jne    7944 <main+0x2eb4>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    6ebd:	48 8d 4d 68          	lea    0x68(%rbp),%rcx
    6ec1:	48 89 cb             	mov    %rcx,%rbx
    6ec4:	48 c1 eb 03          	shr    $0x3,%rbx
    6ec8:	80 bb 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rbx)
    6ecf:	0f 85 67 0a 00 00    	jne    793c <main+0x2eac>
    6ed5:	48 8d 75 58          	lea    0x58(%rbp),%rsi
    6ed9:	45 31 ed             	xor    %r13d,%r13d
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    6edc:	48 89 f0             	mov    %rsi,%rax
    6edf:	48 c1 e8 03          	shr    $0x3,%rax
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    6ee3:	48 83 7d 68 00       	cmpq   $0x0,0x68(%rbp)
    6ee8:	0f 8e 15 01 00 00    	jle    7003 <main+0x2573>
    6eee:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    6ef3:	48 89 74 24 10       	mov    %rsi,0x10(%rsp)
    6ef8:	4c 89 24 24          	mov    %r12,(%rsp)
    6efc:	49 89 c4             	mov    %rax,%r12
    6eff:	90                   	nop
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    6f00:	41 80 bc 24 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r12)
    6f09:	0f 85 23 0a 00 00    	jne    7932 <main+0x2ea2>
    6f0f:	48 8b 55 58          	mov    0x58(%rbp),%rdx
    6f13:	4b 8d 44 ad 00       	lea    0x0(%r13,%r13,4),%rax
    6f18:	48 8d 3c c2          	lea    (%rdx,%rax,8),%rdi
    6f1c:	48 89 f8             	mov    %rdi,%rax
    6f1f:	48 c1 e8 03          	shr    $0x3,%rax
    6f23:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    6f2a:	0f 85 fd 09 00 00    	jne    792d <main+0x2e9d>
    6f30:	48 8d 47 08          	lea    0x8(%rdi),%rax
    6f34:	48 8b 0f             	mov    (%rdi),%rcx
    6f37:	48 89 c2             	mov    %rax,%rdx
    6f3a:	48 c1 ea 03          	shr    $0x3,%rdx
    6f3e:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    6f45:	0f 85 da 09 00 00    	jne    7925 <main+0x2e95>
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
    6f4b:	48 8d 47 10          	lea    0x10(%rdi),%rax
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    6f4f:	48 8b 57 08          	mov    0x8(%rdi),%rdx
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
    6f53:	48 89 c6             	mov    %rax,%rsi
    6f56:	48 c1 ee 03          	shr    $0x3,%rsi
    6f5a:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    6f61:	0f 85 b6 09 00 00    	jne    791d <main+0x2e8d>
    6f67:	48 8d 47 18          	lea    0x18(%rdi),%rax
    6f6b:	4c 8b 47 10          	mov    0x10(%rdi),%r8
    6f6f:	48 89 c6             	mov    %rax,%rsi
    6f72:	48 c1 ee 03          	shr    $0x3,%rsi
    6f76:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    6f7d:	0f 85 92 09 00 00    	jne    7915 <main+0x2e85>
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    6f83:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    6f8d:	49 29 c8             	sub    %rcx,%r8
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    6f90:	48 8b 4f 18          	mov    0x18(%rdi),%rcx
    6f94:	48 29 d1             	sub    %rdx,%rcx
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    6f97:	48 f7 e1             	mul    %rcx
    6f9a:	48 c1 ea 12          	shr    $0x12,%rdx
    6f9e:	49 89 d1             	mov    %rdx,%r9
    6fa1:	48 8d 57 20          	lea    0x20(%rdi),%rdx
    6fa5:	48 89 d0             	mov    %rdx,%rax
    6fa8:	48 c1 e8 03          	shr    $0x3,%rax
    6fac:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    6fb3:	84 c0                	test   %al,%al
    6fb5:	74 08                	je     6fbf <main+0x252f>
    6fb7:	3c 03                	cmp    $0x3,%al
    6fb9:	0f 8e 4e 09 00 00    	jle    790d <main+0x2e7d>
    6fbf:	48 83 ec 08          	sub    $0x8,%rsp
    6fc3:	8b 47 20             	mov    0x20(%rdi),%eax
    6fc6:	ba 02 00 00 00       	mov    $0x2,%edx
    6fcb:	bf 01 00 00 00       	mov    $0x1,%edi
    6fd0:	51                   	push   %rcx
    6fd1:	48 8d 35 08 b9 00 00 	lea    0xb908(%rip),%rsi        # 128e0 <_IO_stdin_used+0x18e0>
    6fd8:	89 c1                	mov    %eax,%ecx
    6fda:	31 c0                	xor    %eax,%eax
    6fdc:	e8 3f d5 ff ff       	call   4520 <__printf_chk@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    6fe1:	80 bb 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rbx)
    6fe8:	5f                   	pop    %rdi
    6fe9:	41 58                	pop    %r8
    6feb:	0f 85 12 09 00 00    	jne    7903 <main+0x2e73>
    6ff1:	49 83 c5 01          	add    $0x1,%r13
    6ff5:	4c 39 6d 68          	cmp    %r13,0x68(%rbp)
    6ff9:	0f 8f 01 ff ff ff    	jg     6f00 <main+0x2470>
    6fff:	4c 8b 24 24          	mov    (%rsp),%r12
    for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    7003:	48 8d bd 84 00 00 00 	lea    0x84(%rbp),%rdi
    700a:	48 89 f8             	mov    %rdi,%rax
    700d:	48 c1 e8 03          	shr    $0x3,%rax
    7011:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    7018:	48 89 f8             	mov    %rdi,%rax
    701b:	83 e0 07             	and    $0x7,%eax
    701e:	83 c0 03             	add    $0x3,%eax
    7021:	38 d0                	cmp    %dl,%al
    7023:	7c 08                	jl     702d <main+0x259d>
    7025:	84 d2                	test   %dl,%dl
    7027:	0f 85 d1 08 00 00    	jne    78fe <main+0x2e6e>
    702d:	8b 85 84 00 00 00    	mov    0x84(%rbp),%eax
    7033:	85 c0                	test   %eax,%eax
    7035:	0f 8e ae 02 00 00    	jle    72e9 <main+0x2859>
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    703b:	48 8d 5d 18          	lea    0x18(%rbp),%rbx
    703f:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    7044:	48 c1 eb 03          	shr    $0x3,%rbx
    7048:	80 bb 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rbx)
    704f:	0f 85 9f 08 00 00    	jne    78f4 <main+0x2e64>
    7055:	4c 89 7c 24 40       	mov    %r15,0x40(%rsp)
    705a:	31 db                	xor    %ebx,%ebx
    705c:	4c 8b 4d 18          	mov    0x18(%rbp),%r9
    7060:	4c 89 74 24 48       	mov    %r14,0x48(%rsp)
    7065:	4c 89 64 24 38       	mov    %r12,0x38(%rsp)
    706a:	49 89 dc             	mov    %rbx,%r12
    706d:	0f 1f 00             	nopl   (%rax)
    7070:	4e 8d 3c e5 00 00 00 00 	lea    0x0(,%r12,8),%r15
    7078:	44 89 e3             	mov    %r12d,%ebx
    707b:	4b 8d 3c 39          	lea    (%r9,%r15,1),%rdi
    707f:	48 89 fa             	mov    %rdi,%rdx
    7082:	48 c1 ea 03          	shr    $0x3,%rdx
    7086:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    708d:	0f 85 d3 06 00 00    	jne    7766 <main+0x2cd6>
    7093:	48 8b 3f             	mov    (%rdi),%rdi
    7096:	48 89 fa             	mov    %rdi,%rdx
    7099:	48 c1 ea 03          	shr    $0x3,%rdx
    709d:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    70a4:	84 d2                	test   %dl,%dl
    70a6:	74 09                	je     70b1 <main+0x2621>
    70a8:	80 fa 03             	cmp    $0x3,%dl
    70ab:	0f 8e b0 06 00 00    	jle    7761 <main+0x2cd1>
    70b1:	8b 0f                	mov    (%rdi),%ecx
    70b3:	85 c9                	test   %ecx,%ecx
    70b5:	0f 8e 12 02 00 00    	jle    72cd <main+0x283d>
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    70bb:	48 8d 47 08          	lea    0x8(%rdi),%rax
    70bf:	48 89 c2             	mov    %rax,%rdx
    70c2:	48 c1 ea 03          	shr    $0x3,%rdx
    70c6:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    70cd:	0f 85 86 06 00 00    	jne    7759 <main+0x2cc9>
    70d3:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    70d8:	4c 8b 47 08          	mov    0x8(%rdi),%r8
    70dc:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
    70e1:	31 f6                	xor    %esi,%esi
    70e3:	49 c1 ed 03          	shr    $0x3,%r13
    70e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    70f0:	49 89 f4             	mov    %rsi,%r12
    70f3:	49 c1 e4 08          	shl    $0x8,%r12
    70f7:	4b 8d 04 20          	lea    (%r8,%r12,1),%rax
    70fb:	48 8d b8 94 00 00 00 	lea    0x94(%rax),%rdi
    7102:	48 89 fa             	mov    %rdi,%rdx
    7105:	48 c1 ea 03          	shr    $0x3,%rdx
    7109:	44 0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%r10d
    7111:	48 89 fa             	mov    %rdi,%rdx
    7114:	83 e2 07             	and    $0x7,%edx
    7117:	83 c2 03             	add    $0x3,%edx
    711a:	44 38 d2             	cmp    %r10b,%dl
    711d:	7c 09                	jl     7128 <main+0x2698>
    711f:	45 84 d2             	test   %r10b,%r10b
    7122:	0f 85 cf 03 00 00    	jne    74f7 <main+0x2a67>
    7128:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    712e:	45 31 f6             	xor    %r14d,%r14d
    7131:	85 d2                	test   %edx,%edx
    7133:	0f 8e 7d 01 00 00    	jle    72b6 <main+0x2826>
    7139:	48 89 34 24          	mov    %rsi,(%rsp)
    713d:	0f 1f 00             	nopl   (%rax)
	  struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    7140:	48 8d b8 88 00 00 00 	lea    0x88(%rax),%rdi
    7147:	48 89 fa             	mov    %rdi,%rdx
    714a:	48 c1 ea 03          	shr    $0x3,%rdx
    714e:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    7155:	0f 85 90 03 00 00    	jne    74eb <main+0x2a5b>
    715b:	4c 89 f7             	mov    %r14,%rdi
    715e:	48 c1 e7 05          	shl    $0x5,%rdi
    7162:	48 03 b8 88 00 00 00 	add    0x88(%rax),%rdi
    7169:	48 8d 47 10          	lea    0x10(%rdi),%rax
    716d:	48 89 c2             	mov    %rax,%rdx
    7170:	48 c1 ea 03          	shr    $0x3,%rdx
    7174:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    717b:	0f 85 62 03 00 00    	jne    74e3 <main+0x2a53>
    7181:	48 8d 47 18          	lea    0x18(%rdi),%rax
    7185:	4c 8b 47 10          	mov    0x10(%rdi),%r8
    7189:	48 89 c2             	mov    %rax,%rdx
    718c:	48 c1 ea 03          	shr    $0x3,%rdx
    7190:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    7197:	0f 85 3e 03 00 00    	jne    74db <main+0x2a4b>
	  struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
    719d:	48 89 f8             	mov    %rdi,%rax
	  struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    71a0:	48 8b 4f 18          	mov    0x18(%rdi),%rcx
	  struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
    71a4:	48 c1 e8 03          	shr    $0x3,%rax
    71a8:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    71af:	0f 85 21 03 00 00    	jne    74d6 <main+0x2a46>
    71b5:	48 8d 47 08          	lea    0x8(%rdi),%rax
    71b9:	48 8b 37             	mov    (%rdi),%rsi
    71bc:	48 89 c2             	mov    %rax,%rdx
    71bf:	48 c1 ea 03          	shr    $0x3,%rdx
    71c3:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    71ca:	0f 85 fe 02 00 00    	jne    74ce <main+0x2a3e>
	  const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    71d0:	48 2b 4f 08          	sub    0x8(%rdi),%rcx
    71d4:	48 83 ec 08          	sub    $0x8,%rsp
    71d8:	49 29 f0             	sub    %rsi,%r8
    71db:	bf 01 00 00 00       	mov    $0x1,%edi
	  printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    71e0:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
    71ea:	51                   	push   %rcx
    71eb:	48 8d 35 6e b7 00 00 	lea    0xb76e(%rip),%rsi        # 12960 <_IO_stdin_used+0x1960>
    71f2:	48 f7 e1             	mul    %rcx
    71f5:	89 d9                	mov    %ebx,%ecx
    71f7:	31 c0                	xor    %eax,%eax
    71f9:	48 c1 ea 12          	shr    $0x12,%rdx
    71fd:	49 89 d1             	mov    %rdx,%r9
    7200:	ba 02 00 00 00       	mov    $0x2,%edx
    7205:	e8 16 d3 ff ff       	call   4520 <__printf_chk@plt>
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    720a:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    7212:	59                   	pop    %rcx
    7213:	5e                   	pop    %rsi
    7214:	0f 85 aa 02 00 00    	jne    74c4 <main+0x2a34>
    721a:	4c 8b 4d 18          	mov    0x18(%rbp),%r9
    721e:	4b 8d 3c 39          	lea    (%r9,%r15,1),%rdi
    7222:	48 89 f8             	mov    %rdi,%rax
    7225:	48 c1 e8 03          	shr    $0x3,%rax
    7229:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    7230:	0f 85 89 02 00 00    	jne    74bf <main+0x2a2f>
    7236:	48 8b 3f             	mov    (%rdi),%rdi
    7239:	48 8d 47 08          	lea    0x8(%rdi),%rax
    723d:	48 89 c2             	mov    %rax,%rdx
    7240:	48 c1 ea 03          	shr    $0x3,%rdx
    7244:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    724b:	0f 85 66 02 00 00    	jne    74b7 <main+0x2a27>
    7251:	4c 8b 47 08          	mov    0x8(%rdi),%r8
    7255:	4b 8d 04 20          	lea    (%r8,%r12,1),%rax
    7259:	48 8d 88 94 00 00 00 	lea    0x94(%rax),%rcx
    7260:	48 89 ca             	mov    %rcx,%rdx
    7263:	48 c1 ea 03          	shr    $0x3,%rdx
    7267:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    726e:	48 89 ca             	mov    %rcx,%rdx
    7271:	83 e2 07             	and    $0x7,%edx
    7274:	83 c2 03             	add    $0x3,%edx
    7277:	40 38 f2             	cmp    %sil,%dl
    727a:	7c 09                	jl     7285 <main+0x27f5>
    727c:	40 84 f6             	test   %sil,%sil
    727f:	0f 85 2a 02 00 00    	jne    74af <main+0x2a1f>
    7285:	49 83 c6 01          	add    $0x1,%r14
    7289:	44 39 b0 94 00 00 00 	cmp    %r14d,0x94(%rax)
    7290:	0f 8f aa fe ff ff    	jg     7140 <main+0x26b0>
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    7296:	48 89 f8             	mov    %rdi,%rax
    7299:	48 8b 34 24          	mov    (%rsp),%rsi
    729d:	48 c1 e8 03          	shr    $0x3,%rax
    72a1:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    72a8:	84 c0                	test   %al,%al
    72aa:	74 08                	je     72b4 <main+0x2824>
    72ac:	3c 03                	cmp    $0x3,%al
    72ae:	0f 8e e2 02 00 00    	jle    7596 <main+0x2b06>
    72b4:	8b 0f                	mov    (%rdi),%ecx
    72b6:	48 83 c6 01          	add    $0x1,%rsi
    72ba:	39 f1                	cmp    %esi,%ecx
    72bc:	0f 8f 2e fe ff ff    	jg     70f0 <main+0x2660>
    for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    72c2:	4c 8b 64 24 08       	mov    0x8(%rsp),%r12
    72c7:	8b 85 84 00 00 00    	mov    0x84(%rbp),%eax
    72cd:	49 83 c4 01          	add    $0x1,%r12
    72d1:	44 39 e0             	cmp    %r12d,%eax
    72d4:	0f 8f 96 fd ff ff    	jg     7070 <main+0x25e0>
    72da:	4c 8b 64 24 38       	mov    0x38(%rsp),%r12
    72df:	4c 8b 7c 24 40       	mov    0x40(%rsp),%r15
    72e4:	4c 8b 74 24 48       	mov    0x48(%rsp),%r14
  for (int x = 0 ; x < thread_count ; x++) {
    72e9:	8b 44 24 28          	mov    0x28(%rsp),%eax
    72ed:	48 81 c5 c0 00 00 00 	add    $0xc0,%rbp
    72f4:	48 83 84 24 80 00 00 00 18 	addq   $0x18,0x80(%rsp)
    72fd:	85 c0                	test   %eax,%eax
    72ff:	75 0d                	jne    730e <main+0x287e>
    7301:	c7 44 24 28 01 00 00 00 	movl   $0x1,0x28(%rsp)
    7309:	e9 87 f8 ff ff       	jmp    6b95 <main+0x2105>
    730e:	4c 89 fa             	mov    %r15,%rdx
    7311:	48 8d 35 c8 b6 00 00 	lea    0xb6c8(%rip),%rsi        # 129e0 <_IO_stdin_used+0x19e0>
    7318:	31 c0                	xor    %eax,%eax
    731a:	4c 89 34 24          	mov    %r14,(%rsp)
    731e:	bf 01 00 00 00       	mov    $0x1,%edi
    7323:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
    7328:	e8 f3 d1 ff ff       	call   4520 <__printf_chk@plt>
    732d:	bf 0a 00 00 00       	mov    $0xa,%edi
    7332:	e8 f9 d1 ff ff       	call   4530 <putchar@plt>
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
    7337:	4c 8b 04 24          	mov    (%rsp),%r8
    733b:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    7340:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    7348:	48 8d 78 08          	lea    0x8(%rax),%rdi
    734c:	48 89 f8             	mov    %rdi,%rax
    734f:	48 c1 e8 03          	shr    $0x3,%rax
    7353:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    735a:	0f 85 94 03 00 00    	jne    76f4 <main+0x2c64>
    7360:	48 8d 35 b9 b6 00 00 	lea    0xb6b9(%rip),%rsi        # 12a20 <_IO_stdin_used+0x1a20>
    7367:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    736f:	bf 01 00 00 00       	mov    $0x1,%edi
    7374:	4c 89 14 24          	mov    %r10,(%rsp)
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    7378:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    7382:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    7387:	48 8b 50 08          	mov    0x8(%rax),%rdx
    738b:	31 c0                	xor    %eax,%eax
    738d:	e8 8e d1 ff ff       	call   4520 <__printf_chk@plt>
    7392:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    7397:	bf 01 00 00 00       	mov    $0x1,%edi
    739c:	48 8d 35 dd b6 00 00 	lea    0xb6dd(%rip),%rsi        # 12a80 <_IO_stdin_used+0x1a80>
    73a3:	4c 89 c0             	mov    %r8,%rax
    73a6:	49 c1 f8 3f          	sar    $0x3f,%r8
    73aa:	48 f7 eb             	imul   %rbx
    73ad:	31 c0                	xor    %eax,%eax
    73af:	48 d1 fa             	sar    %rdx
    73b2:	4c 29 c2             	sub    %r8,%rdx
    73b5:	e8 66 d1 ff ff       	call   4520 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    73ba:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    73bf:	bf 01 00 00 00       	mov    $0x1,%edi
    73c4:	48 8d 35 15 b7 00 00 	lea    0xb715(%rip),%rsi        # 12ae0 <_IO_stdin_used+0x1ae0>
    73cb:	48 f7 eb             	imul   %rbx
    73ce:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    73d3:	48 c1 f8 3f          	sar    $0x3f,%rax
    73d7:	48 d1 fa             	sar    %rdx
    73da:	48 29 c2             	sub    %rax,%rdx
    73dd:	31 c0                	xor    %eax,%eax
    73df:	e8 3c d1 ff ff       	call   4520 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    73e4:	4c 89 f8             	mov    %r15,%rax
    73e7:	49 c1 ff 3f          	sar    $0x3f,%r15
    73eb:	48 8d 35 4e b7 00 00 	lea    0xb74e(%rip),%rsi        # 12b40 <_IO_stdin_used+0x1b40>
    73f2:	48 f7 eb             	imul   %rbx
    73f5:	bf 01 00 00 00       	mov    $0x1,%edi
    73fa:	31 c0                	xor    %eax,%eax
    73fc:	48 d1 fa             	sar    %rdx
    73ff:	4c 29 fa             	sub    %r15,%rdx
    7402:	e8 19 d1 ff ff       	call   4520 <__printf_chk@plt>
  printf("Total sents %ld\n", sents / DURATION);
    7407:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    740c:	bf 01 00 00 00       	mov    $0x1,%edi
    7411:	48 8d 35 68 b7 00 00 	lea    0xb768(%rip),%rsi        # 12b80 <_IO_stdin_used+0x1b80>
    7418:	48 f7 eb             	imul   %rbx
    741b:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7420:	48 c1 f8 3f          	sar    $0x3f,%rax
    7424:	48 d1 fa             	sar    %rdx
    7427:	48 29 c2             	sub    %rax,%rdx
    742a:	31 c0                	xor    %eax,%eax
    742c:	e8 ef d0 ff ff       	call   4520 <__printf_chk@plt>
  printf("Total receives %ld\n", received / DURATION);
    7431:	4c 8b 14 24          	mov    (%rsp),%r10
    7435:	bf 01 00 00 00       	mov    $0x1,%edi
    743a:	48 8d 35 7f b7 00 00 	lea    0xb77f(%rip),%rsi        # 12bc0 <_IO_stdin_used+0x1bc0>
    7441:	4c 89 d0             	mov    %r10,%rax
    7444:	48 f7 eb             	imul   %rbx
    7447:	4c 89 d0             	mov    %r10,%rax
    744a:	48 c1 f8 3f          	sar    $0x3f,%rax
    744e:	48 d1 fa             	sar    %rdx
    7451:	48 29 c2             	sub    %rax,%rdx
    7454:	31 c0                	xor    %eax,%eax
    7456:	e8 c5 d0 ff ff       	call   4520 <__printf_chk@plt>
int main() {
    745b:	48 8b 9c 24 90 00 00 00 	mov    0x90(%rsp),%rbx
    7463:	48 39 9c 24 b0 00 00 00 	cmp    %rbx,0xb0(%rsp)
    746b:	0f 85 54 02 00 00    	jne    76c5 <main+0x2c35>
    7471:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    7479:	48 c7 80 00 80 ff 7f 00 00 00 00 	movq   $0x0,0x7fff8000(%rax)
}
    7484:	48 8b 84 24 18 01 00 00 	mov    0x118(%rsp),%rax
    748c:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    7495:	0f 85 8e 02 00 00    	jne    7729 <main+0x2c99>
    749b:	48 81 c4 28 01 00 00 	add    $0x128,%rsp
    74a2:	31 c0                	xor    %eax,%eax
    74a4:	5b                   	pop    %rbx
    74a5:	5d                   	pop    %rbp
    74a6:	41 5c                	pop    %r12
    74a8:	41 5d                	pop    %r13
    74aa:	41 5e                	pop    %r14
    74ac:	41 5f                	pop    %r15
    74ae:	c3                   	ret
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    74af:	48 89 cf             	mov    %rcx,%rdi
    74b2:	e8 99 d0 ff ff       	call   4550 <__asan_report_load4@plt>
    74b7:	48 89 c7             	mov    %rax,%rdi
    74ba:	e8 21 d0 ff ff       	call   44e0 <__asan_report_load8@plt>
    74bf:	e8 1c d0 ff ff       	call   44e0 <__asan_report_load8@plt>
    74c4:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    74c9:	e8 12 d0 ff ff       	call   44e0 <__asan_report_load8@plt>
	  struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
    74ce:	48 89 c7             	mov    %rax,%rdi
    74d1:	e8 0a d0 ff ff       	call   44e0 <__asan_report_load8@plt>
    74d6:	e8 05 d0 ff ff       	call   44e0 <__asan_report_load8@plt>
	  struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    74db:	48 89 c7             	mov    %rax,%rdi
    74de:	e8 fd cf ff ff       	call   44e0 <__asan_report_load8@plt>
    74e3:	48 89 c7             	mov    %rax,%rdi
    74e6:	e8 f5 cf ff ff       	call   44e0 <__asan_report_load8@plt>
    74eb:	e8 f0 cf ff ff       	call   44e0 <__asan_report_load8@plt>
    long v = 0;
    74f0:	31 d2                	xor    %edx,%edx
    74f2:	e9 64 f7 ff ff       	jmp    6c5b <main+0x21cb>
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    74f7:	e8 54 d0 ff ff       	call   4550 <__asan_report_load4@plt>
              mailboxes[b].lower = &data[0];
    74fc:	4c 89 ff             	mov    %r15,%rdi
    74ff:	e8 cc d1 ff ff       	call   46d0 <__asan_report_store8@plt>
              mailboxes[b].higher = &data[1];
    7504:	48 89 f7             	mov    %rsi,%rdi
    7507:	e8 c4 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
              mailboxes[b].kind = MAILBOX_FRIEND;
    750c:	4c 89 c7             	mov    %r8,%rdi
    750f:	e8 ac d1 ff ff       	call   46c0 <__asan_report_store4@plt>
              data[0].messages = messages;
    7514:	e8 b7 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
              data[1].messages = messages2;
    7519:	48 89 c7             	mov    %rax,%rdi
    751c:	e8 af d1 ff ff       	call   46d0 <__asan_report_store8@plt>
              data[0].messages_limit = messages_limit;
    7521:	48 89 c7             	mov    %rax,%rdi
    7524:	e8 a7 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
              data[0].messages_count = 0;
    7529:	48 89 c7             	mov    %rax,%rdi
    752c:	e8 9f d1 ff ff       	call   46d0 <__asan_report_store8@plt>
              data[1].messages_count = 0;
    7531:	48 89 c7             	mov    %rax,%rdi
    7534:	e8 97 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
              data[1].messages_limit = messages_limit;
    7539:	48 89 c7             	mov    %rax,%rdi
    753c:	e8 8f d1 ff ff       	call   46d0 <__asan_report_store8@plt>
            mailboxes[b].lower = &data[0];
    7541:	48 89 df             	mov    %rbx,%rdi
    7544:	e8 87 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
            mailboxes[b].higher = &data[1];
    7549:	48 89 cf             	mov    %rcx,%rdi
    754c:	e8 7f d1 ff ff       	call   46d0 <__asan_report_store8@plt>
            mailboxes[b].kind = MAILBOX_FOREIGN;
    7551:	48 89 f7             	mov    %rsi,%rdi
    7554:	e8 67 d1 ff ff       	call   46c0 <__asan_report_store4@plt>
            data[0].available = 0;
    7559:	48 89 f7             	mov    %rsi,%rdi
    755c:	e8 5f d1 ff ff       	call   46c0 <__asan_report_store4@plt>
            data[0].messages = messages;
    7561:	e8 6a d1 ff ff       	call   46d0 <__asan_report_store8@plt>
            data[1].messages = messages2;
    7566:	48 89 c7             	mov    %rax,%rdi
    7569:	e8 62 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
            data[1].available = 0;
    756e:	48 89 cf             	mov    %rcx,%rdi
    7571:	e8 4a d1 ff ff       	call   46c0 <__asan_report_store4@plt>
            data[0].messages_limit = messages_limit;
    7576:	48 89 c7             	mov    %rax,%rdi
    7579:	e8 52 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
            data[0].messages_count = 0;
    757e:	48 89 c7             	mov    %rax,%rdi
    7581:	e8 4a d1 ff ff       	call   46d0 <__asan_report_store8@plt>
            data[1].messages_count = 0;
    7586:	48 89 c7             	mov    %rax,%rdi
    7589:	e8 42 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
            data[1].messages_limit = messages_limit;
    758e:	48 89 c7             	mov    %rax,%rdi
    7591:	e8 3a d1 ff ff       	call   46d0 <__asan_report_store8@plt>
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    7596:	e8 b5 cf ff ff       	call   4550 <__asan_report_load4@plt>
    thread_data[x].thread_count = 2;
    759b:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    75a0:	e8 1b d1 ff ff       	call   46c0 <__asan_report_store4@plt>
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    75a5:	e8 16 d1 ff ff       	call   46c0 <__asan_report_store4@plt>
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    75aa:	e8 11 d1 ff ff       	call   46c0 <__asan_report_store4@plt>
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    75af:	e8 0c d1 ff ff       	call   46c0 <__asan_report_store4@plt>
        thread_data[x].tasks[barrier_count].arrived = 0; 
    75b4:	e8 07 d1 ff ff       	call   46c0 <__asan_report_store4@plt>
        thread_data[x].tasks[barrier_count].available = 1; 
    75b9:	e8 02 d1 ff ff       	call   46c0 <__asan_report_store4@plt>
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    75be:	e8 0d d1 ff ff       	call   46d0 <__asan_report_store8@plt>
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    75c3:	e8 08 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
    75c8:	e8 03 d1 ff ff       	call   46d0 <__asan_report_store8@plt>
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    75cd:	e8 fe d0 ff ff       	call   46d0 <__asan_report_store8@plt>
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    75d2:	48 89 c7             	mov    %rax,%rdi
    75d5:	e8 f6 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
        thread_data[x].buffers_count = buffers_per_thread;
    75da:	e8 e1 d0 ff ff       	call   46c0 <__asan_report_store4@plt>
               thread_data[x].tasks[y].run = barriered_work; 
    75df:	e8 ec d0 ff ff       	call   46d0 <__asan_report_store8@plt>
          thread_data[x].tasks[y].task_index = y;
    75e4:	e8 d7 d0 ff ff       	call   46c0 <__asan_report_store4@plt>
    my_thread_data[n] = &thread_data[n]; 
    75e9:	48 89 c7             	mov    %rax,%rdi
    75ec:	e8 df d0 ff ff       	call   46d0 <__asan_report_store8@plt>
    75f1:	48 89 c7             	mov    %rax,%rdi
    75f4:	e8 d7 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
    75f9:	48 89 c7             	mov    %rax,%rdi
    75fc:	e8 cf d0 ff ff       	call   46d0 <__asan_report_store8@plt>
    7601:	48 89 c7             	mov    %rax,%rdi
    7604:	e8 c7 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
    7609:	48 89 c7             	mov    %rax,%rdi
    760c:	e8 bf d0 ff ff       	call   46d0 <__asan_report_store8@plt>
    7611:	48 89 c7             	mov    %rax,%rdi
    7614:	e8 b7 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
    7619:	48 89 c7             	mov    %rax,%rdi
    761c:	e8 af d0 ff ff       	call   46d0 <__asan_report_store8@plt>
    7621:	e8 aa d0 ff ff       	call   46d0 <__asan_report_store8@plt>
          thread_data[x].tasks[y].sending = 1;
    7626:	e8 95 d0 ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].message = messaged;
    762b:	e8 a0 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    7630:	e8 8b d0 ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    7635:	48 89 df             	mov    %rbx,%rdi
    7638:	e8 83 d0 ff ff       	call   46c0 <__asan_report_store4@plt>
    763d:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    7642:	e8 99 ce ff ff       	call   44e0 <__asan_report_load8@plt>
          messaged->thread_index = thread_data[x].thread_index;
    7647:	e8 84 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
    764c:	48 89 df             	mov    %rbx,%rdi
    764f:	e8 fc ce ff ff       	call   4550 <__asan_report_load4@plt>
          messaged->task_index = y;
    7654:	e8 77 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
          thread_data[x].tasks[y].worker_count = thread_count;
    7659:	e8 62 d0 ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].task_count = total_barrier_count;
    765e:	e8 5d d0 ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
    7663:	e8 58 d0 ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].all_thread_count = thread_count;
    7668:	e8 53 d0 ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].total_thread_count = thread_count;
    766d:	e8 4e d0 ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].thread_count = 2;
    7672:	e8 49 d0 ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].arrived = 0;
    7677:	e8 44 d0 ff ff       	call   46c0 <__asan_report_store4@plt>
          thread_data[x].tasks[y].available = 1;
    767c:	e8 3f d0 ff ff       	call   46c0 <__asan_report_store4@plt>
            exit(1);
    7681:	e8 8a cf ff ff       	call   4610 <__asan_handle_no_return@plt>
    7686:	bf 01 00 00 00       	mov    $0x1,%edi
    768b:	e8 80 ce ff ff       	call   4510 <exit@plt>
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    7690:	e8 3b d0 ff ff       	call   46d0 <__asan_report_store8@plt>
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    7695:	e8 26 d0 ff ff       	call   46c0 <__asan_report_store4@plt>
    769a:	e8 b1 ce ff ff       	call   4550 <__asan_report_load4@plt>
    769f:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    76a4:	e8 37 ce ff ff       	call   44e0 <__asan_report_load8@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
    76a9:	e8 22 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    76ae:	e8 1d d0 ff ff       	call   46d0 <__asan_report_store8@plt>
          thread_data[x].tasks[y].snapshot_count = 99;
    76b3:	e8 18 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
  thread_data[timer_threadi].threads = my_thread_data;
    76b8:	48 89 c7             	mov    %rax,%rdi
    76bb:	e8 10 d0 ff ff       	call   46d0 <__asan_report_store8@plt>
    thread_data[n].tasks[0].scheduled = 1;
    76c0:	e8 1b ce ff ff       	call   44e0 <__asan_report_load8@plt>
int main() {
    76c5:	48 c7 03 0e 36 e0 45 	movq   $0x45e0360e,(%rbx)
    76cc:	48 89 d8             	mov    %rbx,%rax
    76cf:	48 8b 9c 24 a8 00 00 00 	mov    0xa8(%rsp),%rbx
    76d7:	48 be f5 f5 f5 f5 f5 f5 f5 f5 	movabs $0xf5f5f5f5f5f5f5f5,%rsi
    76e1:	48 89 b3 00 80 ff 7f 	mov    %rsi,0x7fff8000(%rbx)
    76e8:	48 8b 40 38          	mov    0x38(%rax),%rax
    76ec:	c6 00 00             	movb   $0x0,(%rax)
    76ef:	e9 90 fd ff ff       	jmp    7484 <main+0x29f4>
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
    76f4:	e8 e7 cd ff ff       	call   44e0 <__asan_report_load8@plt>
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    76f9:	e8 d2 cf ff ff       	call   46d0 <__asan_report_store8@plt>
    buffers[x].count = buffer_size;
    76fe:	4c 89 ef             	mov    %r13,%rdi
    7701:	e8 ba cf ff ff       	call   46c0 <__asan_report_store4@plt>
int main() {
    7706:	bf 40 00 00 00       	mov    $0x40,%edi
    770b:	e8 a0 d0 ff ff       	call   47b0 <__asan_stack_malloc_0@plt>
    7710:	48 85 c0             	test   %rax,%rax
    7713:	48 0f 44 84 24 90 00 00 00 	cmove  0x90(%rsp),%rax
    771c:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
    7724:	e9 a4 d3 ff ff       	jmp    4acd <main+0x3d>
}
    7729:	e8 82 cf ff ff       	call   46b0 <__stack_chk_fail@plt>
      thread_data[x].other = other;
    772e:	e8 8d cf ff ff       	call   46c0 <__asan_report_store4@plt>
        my_thread_data[0] = &thread_data[other]; 
    7733:	4c 89 e7             	mov    %r12,%rdi
    7736:	e8 95 cf ff ff       	call   46d0 <__asan_report_store8@plt>
        my_thread_data[1] = &thread_data[x]; 
    773b:	e8 90 cf ff ff       	call   46d0 <__asan_report_store8@plt>
        thread_data[x].protected_state = &protected_state[k];
    7740:	e8 8b cf ff ff       	call   46d0 <__asan_report_store8@plt>
        thread_data[x].thread_index = 1;
    7745:	e8 76 cf ff ff       	call   46c0 <__asan_report_store4@plt>
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    774a:	e8 81 cf ff ff       	call   46d0 <__asan_report_store8@plt>
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    774f:	e8 6c cf ff ff       	call   46c0 <__asan_report_store4@plt>
      buffers[x].buffer[y].available = 0;
    7754:	e8 67 cf ff ff       	call   46c0 <__asan_report_store4@plt>
	for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    7759:	48 89 c7             	mov    %rax,%rdi
    775c:	e8 7f cd ff ff       	call   44e0 <__asan_report_load8@plt>
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    7761:	e8 ea cd ff ff       	call   4550 <__asan_report_load4@plt>
    7766:	e8 75 cd ff ff       	call   44e0 <__asan_report_load8@plt>
      thread_data[x].timestamp_limit = timestamp_limit;
    776b:	e8 60 cf ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].timestamp_count = 0;
    7770:	e8 5b cf ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    7775:	e8 56 cf ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    777a:	e8 51 cf ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].task_count = total_barrier_count;
    777f:	e8 3c cf ff ff       	call   46c0 <__asan_report_store4@plt>
      thread_data[x].total_thread_count = total_threads;
    7784:	e8 37 cf ff ff       	call   46c0 <__asan_report_store4@plt>
      thread_data[x].thread_count = 2;
    7789:	e8 32 cf ff ff       	call   46c0 <__asan_report_store4@plt>
      thread_data[x].all_threads = thread_data;
    778e:	e8 3d cf ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].threads = my_thread_data;
    7793:	e8 38 cf ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].real_thread_index = x;
    7798:	e8 23 cf ff ff       	call   46c0 <__asan_report_store4@plt>
      thread_data[x].cpu_set = sendercpu;
    779d:	e8 2e cf ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].kind = KERNEL_THREAD;
    77a2:	4c 89 d7             	mov    %r10,%rdi
    77a5:	e8 16 cf ff ff       	call   46c0 <__asan_report_store4@plt>
          CPU_SET(curcpu, sendercpu);
    77aa:	e8 31 cd ff ff       	call   44e0 <__asan_report_load8@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    77af:	e8 2c cd ff ff       	call   44e0 <__asan_report_load8@plt>
      thread_data[x].running = 1;
    77b4:	e8 07 cf ff ff       	call   46c0 <__asan_report_store4@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    77b9:	4c 89 e7             	mov    %r12,%rdi
    77bc:	e8 1f cd ff ff       	call   44e0 <__asan_report_load8@plt>
      thread_data[x].type = WORKER;
    77c1:	e8 fa ce ff ff       	call   46c0 <__asan_report_store4@plt>
      my_thread_data[n] = &thread_data[n]; 
    77c6:	48 89 c7             	mov    %rax,%rdi
    77c9:	e8 02 cf ff ff       	call   46d0 <__asan_report_store8@plt>
    77ce:	e8 fd ce ff ff       	call   46d0 <__asan_report_store8@plt>
    thread_data[x].threads = my_thread_data;
    77d3:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    77d8:	e8 f3 ce ff ff       	call   46d0 <__asan_report_store8@plt>
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    77dd:	e8 ee ce ff ff       	call   46d0 <__asan_report_store8@plt>
    my_thread_data[n] = &thread_data[n]; 
    77e2:	48 89 c7             	mov    %rax,%rdi
    77e5:	e8 e6 ce ff ff       	call   46d0 <__asan_report_store8@plt>
    77ea:	48 89 c7             	mov    %rax,%rdi
    77ed:	e8 de ce ff ff       	call   46d0 <__asan_report_store8@plt>
    77f2:	48 89 c7             	mov    %rax,%rdi
    77f5:	e8 d6 ce ff ff       	call   46d0 <__asan_report_store8@plt>
    77fa:	48 89 c7             	mov    %rax,%rdi
    77fd:	e8 ce ce ff ff       	call   46d0 <__asan_report_store8@plt>
    7802:	48 89 c7             	mov    %rax,%rdi
    7805:	e8 c6 ce ff ff       	call   46d0 <__asan_report_store8@plt>
    780a:	48 89 c7             	mov    %rax,%rdi
    780d:	e8 be ce ff ff       	call   46d0 <__asan_report_store8@plt>
    7812:	48 89 c7             	mov    %rax,%rdi
    7815:	e8 b6 ce ff ff       	call   46d0 <__asan_report_store8@plt>
    781a:	48 89 c7             	mov    %rax,%rdi
    781d:	e8 ae ce ff ff       	call   46d0 <__asan_report_store8@plt>
            thread_data[x].tasks[y].run = barriered_work; 
    7822:	e8 a9 ce ff ff       	call   46d0 <__asan_report_store8@plt>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    7827:	e8 94 ce ff ff       	call   46c0 <__asan_report_store4@plt>
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    782c:	e8 8f ce ff ff       	call   46c0 <__asan_report_store4@plt>
        thread_data[x].tasks = barriers;
    7831:	4c 89 cf             	mov    %r9,%rdi
    7834:	e8 97 ce ff ff       	call   46d0 <__asan_report_store8@plt>
    thread_data[x].threads = my_thread_data;
    7839:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    783e:	e8 8d ce ff ff       	call   46d0 <__asan_report_store8@plt>
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    7843:	48 89 c7             	mov    %rax,%rdi
    7846:	e8 85 ce ff ff       	call   46d0 <__asan_report_store8@plt>
    my_thread_data[0] = &thread_data[x]; 
    784b:	e8 80 ce ff ff       	call   46d0 <__asan_report_store8@plt>
            CPU_SET(j, sendercpu);
    7850:	4c 89 ff             	mov    %r15,%rdi
    7853:	e8 88 cc ff ff       	call   44e0 <__asan_report_load8@plt>
      thread_data[x].task_timestamp_limit = timestamp_limit;
    7858:	e8 73 ce ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].task_timestamp_count = 0;
    785d:	e8 6e ce ff ff       	call   46d0 <__asan_report_store8@plt>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    7862:	e8 69 ce ff ff       	call   46d0 <__asan_report_store8@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    7867:	e8 64 ce ff ff       	call   46d0 <__asan_report_store8@plt>
          messaged->message = message;
    786c:	4c 89 df             	mov    %r11,%rdi
    786f:	e8 5c ce ff ff       	call   46d0 <__asan_report_store8@plt>
          thread_data[x].tasks[y].protected = do_protected_write; 
    7874:	e8 57 ce ff ff       	call   46d0 <__asan_report_store8@plt>
  thread_data[timer_threadi].running = 1;
    7879:	e8 42 ce ff ff       	call   46c0 <__asan_report_store4@plt>
  thread_data[timer_threadi].type = TIMER;
    787e:	e8 3d ce ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[n].tasks[0].scheduled = 1;
    7883:	e8 38 ce ff ff       	call   46c0 <__asan_report_store4@plt>
    7888:	e8 33 ce ff ff       	call   46c0 <__asan_report_store4@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
    788d:	4c 89 f7             	mov    %r14,%rdi
    7890:	e8 bb cc ff ff       	call   4550 <__asan_report_load4@plt>
    thread_data[x].thread_index = x;
    7895:	e8 26 ce ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].total_thread_count = total_threads;
    789a:	e8 21 ce ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].thread_count = thread_count;
    789f:	e8 1c ce ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].threads = my_thread_data;
    78a4:	48 89 c7             	mov    %rax,%rdi
    78a7:	e8 24 ce ff ff       	call   46d0 <__asan_report_store8@plt>
      my_thread_data[n] = &thread_data[n]; 
    78ac:	48 89 c7             	mov    %rax,%rdi
    78af:	e8 1c ce ff ff       	call   46d0 <__asan_report_store8@plt>
    78b4:	e8 17 ce ff ff       	call   46d0 <__asan_report_store8@plt>
	  thread_data[x].buffers_count = 1;
    78b9:	e8 02 ce ff ff       	call   46c0 <__asan_report_store4@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    78be:	e8 0d ce ff ff       	call   46d0 <__asan_report_store8@plt>
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    78c3:	48 89 c7             	mov    %rax,%rdi
    78c6:	e8 05 ce ff ff       	call   46d0 <__asan_report_store8@plt>
    thread_data[x].task_count = 0;
    78cb:	e8 f0 cd ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].running = 1;
    78d0:	e8 eb cd ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].type = EXTERNAL;
    78d5:	48 89 ef             	mov    %rbp,%rdi
    78d8:	e8 e3 cd ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].thread_index = x;
    78dd:	4c 89 ff             	mov    %r15,%rdi
    78e0:	e8 db cd ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].thread_count = thread_count;
    78e5:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    78ea:	e8 d1 cd ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    78ef:	e8 cc cd ff ff       	call   46c0 <__asan_report_store4@plt>
      for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    78f4:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    78f9:	e8 e2 cb ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    78fe:	e8 4d cc ff ff       	call   4550 <__asan_report_load4@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    7903:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    7908:	e8 d3 cb ff ff       	call   44e0 <__asan_report_load8@plt>
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    790d:	48 89 d7             	mov    %rdx,%rdi
    7910:	e8 3b cc ff ff       	call   4550 <__asan_report_load4@plt>
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
    7915:	48 89 c7             	mov    %rax,%rdi
    7918:	e8 c3 cb ff ff       	call   44e0 <__asan_report_load8@plt>
    791d:	48 89 c7             	mov    %rax,%rdi
    7920:	e8 bb cb ff ff       	call   44e0 <__asan_report_load8@plt>
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
    7925:	48 89 c7             	mov    %rax,%rdi
    7928:	e8 b3 cb ff ff       	call   44e0 <__asan_report_load8@plt>
    792d:	e8 ae cb ff ff       	call   44e0 <__asan_report_load8@plt>
    7932:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    7937:	e8 a4 cb ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    793c:	48 89 cf             	mov    %rcx,%rdi
    793f:	e8 9c cb ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
    7944:	e8 97 cb ff ff       	call   44e0 <__asan_report_load8@plt>
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    7949:	48 89 d7             	mov    %rdx,%rdi
    794c:	e8 8f cb ff ff       	call   44e0 <__asan_report_load8@plt>
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    7951:	48 89 d7             	mov    %rdx,%rdi
    7954:	e8 87 cb ff ff       	call   44e0 <__asan_report_load8@plt>
    thread_data[n].tasks[0].scheduled = 1;
    7959:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    795e:	e8 7d cb ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    7963:	4c 89 ef             	mov    %r13,%rdi
    7966:	e8 e5 cb ff ff       	call   4550 <__asan_report_load4@plt>
      v += thread_data[me].tasks[n].v;
    796b:	e8 70 cb ff ff       	call   44e0 <__asan_report_load8@plt>
    7970:	48 89 ef             	mov    %rbp,%rdi
    7973:	e8 68 cb ff ff       	call   44e0 <__asan_report_load8@plt>
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    7978:	48 8b bc 24 80 00 00 00 	mov    0x80(%rsp),%rdi
    7980:	e8 5b cb ff ff       	call   44e0 <__asan_report_load8@plt>
      v += thread_data[other].tasks[n].v;
    7985:	e8 56 cb ff ff       	call   44e0 <__asan_report_load8@plt>
    798a:	e8 51 cb ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    798f:	e8 bc cb ff ff       	call   4550 <__asan_report_load4@plt>
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
    7994:	48 89 d7             	mov    %rdx,%rdi
    7997:	e8 44 cb ff ff       	call   44e0 <__asan_report_load8@plt>
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
    799c:	48 89 d7             	mov    %rdx,%rdi
    799f:	e8 3c cb ff ff       	call   44e0 <__asan_report_load8@plt>
    79a4:	48 89 c7             	mov    %rax,%rdi
    79a7:	e8 34 cb ff ff       	call   44e0 <__asan_report_load8@plt>
      sends += thread_data[x].tasks[n].sends;
    79ac:	48 89 c7             	mov    %rax,%rdi
    79af:	e8 2c cb ff ff       	call   44e0 <__asan_report_load8@plt>
      ingests += thread_data[x].tasks[n].ingest_count;
    79b4:	48 89 c7             	mov    %rax,%rdi
    79b7:	e8 24 cb ff ff       	call   44e0 <__asan_report_load8@plt>
      total += thread_data[x].tasks[n].n;
    79bc:	e8 1f cb ff ff       	call   44e0 <__asan_report_load8@plt>
    79c1:	48 89 ef             	mov    %rbp,%rdi
    79c4:	e8 17 cb ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    79c9:	4c 89 ef             	mov    %r13,%rdi
    79cc:	e8 7f cb ff ff       	call   4550 <__asan_report_load4@plt>
    printf("Total Protected %ld\n", protected_state[me].protected);
    79d1:	48 8b bc 24 80 00 00 00 	mov    0x80(%rsp),%rdi
    79d9:	e8 02 cb ff ff       	call   44e0 <__asan_report_load8@plt>
    pthread_join(thread[x], &result);
    79de:	4c 89 ef             	mov    %r13,%rdi
    79e1:	e8 fa ca ff ff       	call   44e0 <__asan_report_load8@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
    79e6:	e8 65 cb ff ff       	call   4550 <__asan_report_load4@plt>
    thread_data[x].task_count = 0;
    79eb:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    79f0:	e8 cb cc ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].running = 1;
    79f5:	e8 c6 cc ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].type = IO;
    79fa:	e8 c1 cc ff ff       	call   46c0 <__asan_report_store4@plt>
  thread_data[timer_threadi].thread_index = 0;
    79ff:	e8 bc cc ff ff       	call   46c0 <__asan_report_store4@plt>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    7a04:	e8 b7 cc ff ff       	call   46c0 <__asan_report_store4@plt>
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    7a09:	e8 b2 cc ff ff       	call   46c0 <__asan_report_store4@plt>
  thread_data[timer_threadi].total_thread_count = total_threads;
    7a0e:	e8 ad cc ff ff       	call   46c0 <__asan_report_store4@plt>
  thread_data[timer_threadi].task_count = total_barrier_count;
    7a13:	e8 a8 cc ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].task_count = total_barrier_count;
    7a18:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    7a1d:	e8 9e cc ff ff       	call   46c0 <__asan_report_store4@plt>
    thread_data[x].thread_index = 0;
    7a22:	4c 89 ff             	mov    %r15,%rdi
    7a25:	e8 96 cc ff ff       	call   46c0 <__asan_report_store4@plt>
    7a2a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000007a30 <_sub_I_00099_1>:
}
    7a30:	f3 0f 1e fa          	endbr64
    7a34:	48 83 ec 08          	sub    $0x8,%rsp
    7a38:	e8 73 ca ff ff       	call   44b0 <__asan_init@plt>
    7a3d:	e8 ce cd ff ff       	call   4810 <__asan_version_mismatch_check_v8@plt>
    7a42:	be 69 00 00 00       	mov    $0x69,%esi
    7a47:	48 8d 3d 72 d6 00 00 	lea    0xd672(%rip),%rdi        # 150c0 <unimplemented_content+0x60>
    7a4e:	48 83 c4 08          	add    $0x8,%rsp
    7a52:	e9 09 cd ff ff       	jmp    4760 <__asan_register_globals@plt>
    7a57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000007a60 <_start>:
    7a60:	f3 0f 1e fa          	endbr64
    7a64:	31 ed                	xor    %ebp,%ebp
    7a66:	49 89 d1             	mov    %rdx,%r9
    7a69:	5e                   	pop    %rsi
    7a6a:	48 89 e2             	mov    %rsp,%rdx
    7a6d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    7a71:	50                   	push   %rax
    7a72:	54                   	push   %rsp
    7a73:	45 31 c0             	xor    %r8d,%r8d
    7a76:	31 c9                	xor    %ecx,%ecx
    7a78:	48 8d 3d 11 d0 ff ff 	lea    -0x2fef(%rip),%rdi        # 4a90 <main>
    7a7f:	ff 15 73 d5 00 00    	call   *0xd573(%rip)        # 14ff8 <__libc_start_main@GLIBC_2.34>
    7a85:	f4                   	hlt
    7a86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000007a90 <deregister_tm_clones>:
    7a90:	48 8d 3d 69 f0 00 00 	lea    0xf069(%rip),%rdi        # 16b00 <__asan_option_detect_stack_use_after_return@@Base>
    7a97:	48 8d 05 62 f0 00 00 	lea    0xf062(%rip),%rax        # 16b00 <__asan_option_detect_stack_use_after_return@@Base>
    7a9e:	48 39 f8             	cmp    %rdi,%rax
    7aa1:	74 15                	je     7ab8 <deregister_tm_clones+0x28>
    7aa3:	48 8b 05 36 d5 00 00 	mov    0xd536(%rip),%rax        # 14fe0 <_ITM_deregisterTMCloneTable@Base>
    7aaa:	48 85 c0             	test   %rax,%rax
    7aad:	74 09                	je     7ab8 <deregister_tm_clones+0x28>
    7aaf:	ff e0                	jmp    *%rax
    7ab1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7ab8:	c3                   	ret
    7ab9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000007ac0 <register_tm_clones>:
    7ac0:	48 8d 3d 39 f0 00 00 	lea    0xf039(%rip),%rdi        # 16b00 <__asan_option_detect_stack_use_after_return@@Base>
    7ac7:	48 8d 35 32 f0 00 00 	lea    0xf032(%rip),%rsi        # 16b00 <__asan_option_detect_stack_use_after_return@@Base>
    7ace:	48 29 fe             	sub    %rdi,%rsi
    7ad1:	48 89 f0             	mov    %rsi,%rax
    7ad4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    7ad8:	48 c1 f8 03          	sar    $0x3,%rax
    7adc:	48 01 c6             	add    %rax,%rsi
    7adf:	48 d1 fe             	sar    %rsi
    7ae2:	74 14                	je     7af8 <register_tm_clones+0x38>
    7ae4:	48 8b 05 fd d4 00 00 	mov    0xd4fd(%rip),%rax        # 14fe8 <_ITM_registerTMCloneTable@Base>
    7aeb:	48 85 c0             	test   %rax,%rax
    7aee:	74 08                	je     7af8 <register_tm_clones+0x38>
    7af0:	ff e0                	jmp    *%rax
    7af2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    7af8:	c3                   	ret
    7af9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000007b00 <__do_global_dtors_aux>:
    7b00:	f3 0f 1e fa          	endbr64
    7b04:	80 3d 1d f0 00 00 00 	cmpb   $0x0,0xf01d(%rip)        # 16b28 <completed.0>
    7b0b:	75 2b                	jne    7b38 <__do_global_dtors_aux+0x38>
    7b0d:	55                   	push   %rbp
    7b0e:	48 83 3d da d4 00 00 00 	cmpq   $0x0,0xd4da(%rip)        # 14ff0 <__cxa_finalize@GLIBC_2.2.5>
    7b16:	48 89 e5             	mov    %rsp,%rbp
    7b19:	74 0c                	je     7b27 <__do_global_dtors_aux+0x27>
    7b1b:	48 8b 3d e6 d4 00 00 	mov    0xd4e6(%rip),%rdi        # 15008 <__dso_handle>
    7b22:	e8 09 c9 ff ff       	call   4430 <__cxa_finalize@plt>
    7b27:	e8 64 ff ff ff       	call   7a90 <deregister_tm_clones>
    7b2c:	c6 05 f5 ef 00 00 01 	movb   $0x1,0xeff5(%rip)        # 16b28 <completed.0>
    7b33:	5d                   	pop    %rbp
    7b34:	c3                   	ret
    7b35:	0f 1f 00             	nopl   (%rax)
    7b38:	c3                   	ret
    7b39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000007b40 <frame_dummy>:
    7b40:	f3 0f 1e fa          	endbr64
    7b44:	e9 77 ff ff ff       	jmp    7ac0 <register_tm_clones>
    7b49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000007b50 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    7b50:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    7b54:	48 8d 87 28 01 00 00 	lea    0x128(%rdi),%rax
int do_protected_write(struct BarrierTask *data) {
    7b5b:	48 83 ec 08          	sub    $0x8,%rsp
  struct ProtectedState *protected = data->thread->protected_state;
    7b5f:	48 89 c2             	mov    %rax,%rdx
    7b62:	48 c1 ea 03          	shr    $0x3,%rdx
    7b66:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    7b6d:	0f 85 8e 00 00 00    	jne    7c01 <do_protected_write+0xb1>
    7b73:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    7b7a:	48 8d 50 48          	lea    0x48(%rax),%rdx
    7b7e:	48 89 d1             	mov    %rdx,%rcx
    7b81:	48 c1 e9 03          	shr    $0x3,%rcx
    7b85:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    7b8c:	0f 85 8c 00 00 00    	jne    7c1e <do_protected_write+0xce>
  data->v++; // thread local
    7b92:	48 8d 97 10 01 00 00 	lea    0x110(%rdi),%rdx
  struct ProtectedState *protected = data->thread->protected_state;
    7b99:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    7b9d:	48 89 d1             	mov    %rdx,%rcx
    7ba0:	48 c1 e9 03          	shr    $0x3,%rcx
    7ba4:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    7bab:	75 69                	jne    7c16 <do_protected_write+0xc6>
  protected->protected++; // shared between all threads
    7bad:	48 89 c2             	mov    %rax,%rdx
  data->v++; // thread local
    7bb0:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  protected->protected++; // shared between all threads
    7bb8:	48 c1 ea 03          	shr    $0x3,%rdx
    7bbc:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    7bc3:	75 49                	jne    7c0e <do_protected_write+0xbe>
  if (protected->balance > 0) {
    7bc5:	48 8d 78 08          	lea    0x8(%rax),%rdi
  protected->protected++; // shared between all threads
    7bc9:	48 83 00 01          	addq   $0x1,(%rax)
  if (protected->balance > 0) {
    7bcd:	48 89 fa             	mov    %rdi,%rdx
    7bd0:	48 c1 ea 03          	shr    $0x3,%rdx
    7bd4:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    7bdb:	75 2c                	jne    7c09 <do_protected_write+0xb9>
    7bdd:	48 8b 48 08          	mov    0x8(%rax),%rcx
    protected->balance -= 500; // shared between all threads
    7be1:	48 85 c9             	test   %rcx,%rcx
    7be4:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    7beb:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    7bf2:	48 0f 4f d6          	cmovg  %rsi,%rdx
    7bf6:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    7bfa:	31 c0                	xor    %eax,%eax
    7bfc:	48 83 c4 08          	add    $0x8,%rsp
    7c00:	c3                   	ret
  struct ProtectedState *protected = data->thread->protected_state;
    7c01:	48 89 c7             	mov    %rax,%rdi
    7c04:	e8 d7 c8 ff ff       	call   44e0 <__asan_report_load8@plt>
  if (protected->balance > 0) {
    7c09:	e8 d2 c8 ff ff       	call   44e0 <__asan_report_load8@plt>
  protected->protected++; // shared between all threads
    7c0e:	48 89 c7             	mov    %rax,%rdi
    7c11:	e8 ca c8 ff ff       	call   44e0 <__asan_report_load8@plt>
  data->v++; // thread local
    7c16:	48 89 d7             	mov    %rdx,%rdi
    7c19:	e8 c2 c8 ff ff       	call   44e0 <__asan_report_load8@plt>
  struct ProtectedState *protected = data->thread->protected_state;
    7c1e:	48 89 d7             	mov    %rdx,%rdi
    7c21:	e8 ba c8 ff ff       	call   44e0 <__asan_report_load8@plt>
    7c26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000007c30 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    7c30:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    7c34:	48 8d 97 48 01 00 00 	lea    0x148(%rdi),%rdx
int barriered_reset(struct BarrierTask *data) {
    7c3b:	48 83 ec 08          	sub    $0x8,%rsp
    for (int x = 0 ; x < data->task_count ; x++) {
    7c3f:	48 89 d0             	mov    %rdx,%rax
    7c42:	48 c1 e8 03          	shr    $0x3,%rax
    7c46:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    7c4d:	84 c0                	test   %al,%al
    7c4f:	74 08                	je     7c59 <barriered_reset+0x29>
    7c51:	3c 03                	cmp    $0x3,%al
    7c53:	0f 8e 6b 01 00 00    	jle    7dc4 <barriered_reset+0x194>
    7c59:	48 63 97 48 01 00 00 	movslq 0x148(%rdi),%rdx
    7c60:	85 d2                	test   %edx,%edx
    7c62:	0f 8e 52 01 00 00    	jle    7dba <barriered_reset+0x18a>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    7c68:	48 8d 87 28 01 00 00 	lea    0x128(%rdi),%rax
    7c6f:	48 89 c1             	mov    %rax,%rcx
    7c72:	48 c1 e9 03          	shr    $0x3,%rcx
    7c76:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    7c7d:	0f 85 6e 01 00 00    	jne    7df1 <barriered_reset+0x1c1>
    7c83:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    7c8a:	48 8d 48 18          	lea    0x18(%rax),%rcx
    7c8e:	48 89 ce             	mov    %rcx,%rsi
    7c91:	48 c1 ee 03          	shr    $0x3,%rsi
    7c95:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    7c9c:	0f 85 3f 01 00 00    	jne    7de1 <barriered_reset+0x1b1>
    7ca2:	48 8d b7 30 01 00 00 	lea    0x130(%rdi),%rsi
    7ca9:	4c 8b 40 18          	mov    0x18(%rax),%r8
    7cad:	48 89 f1             	mov    %rsi,%rcx
    7cb0:	48 c1 e9 03          	shr    $0x3,%rcx
    7cb4:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    7cbb:	84 c9                	test   %cl,%cl
    7cbd:	74 09                	je     7cc8 <barriered_reset+0x98>
    7cbf:	80 f9 03             	cmp    $0x3,%cl
    7cc2:	0f 8e 21 01 00 00    	jle    7de9 <barriered_reset+0x1b9>
    7cc8:	48 63 8f 30 01 00 00 	movslq 0x130(%rdi),%rcx
    7ccf:	49 8d 3c c8          	lea    (%r8,%rcx,8),%rdi
    7cd3:	48 89 f9             	mov    %rdi,%rcx
    7cd6:	48 c1 e9 03          	shr    $0x3,%rcx
    7cda:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    7ce1:	0f 85 17 01 00 00    	jne    7dfe <barriered_reset+0x1ce>
    7ce7:	48 8b 0f             	mov    (%rdi),%rcx
    7cea:	48 8d 79 38          	lea    0x38(%rcx),%rdi
    7cee:	48 89 fe             	mov    %rdi,%rsi
    7cf1:	48 c1 ee 03          	shr    $0x3,%rsi
    7cf5:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    7cfc:	0f 85 f7 00 00 00    	jne    7df9 <barriered_reset+0x1c9>
      data->thread->tasks[x].available = 1; 
    7d02:	48 8d 78 38          	lea    0x38(%rax),%rdi
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    7d06:	48 8b 49 38          	mov    0x38(%rcx),%rcx
      data->thread->tasks[x].available = 1; 
    7d0a:	48 89 fe             	mov    %rdi,%rsi
    7d0d:	48 c1 ee 03          	shr    $0x3,%rsi
    7d11:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    7d18:	0f 85 e5 00 00 00    	jne    7e03 <barriered_reset+0x1d3>
    7d1e:	48 8b 40 38          	mov    0x38(%rax),%rax
    7d22:	48 c1 e2 09          	shl    $0x9,%rdx
    7d26:	48 8d b9 80 00 00 00 	lea    0x80(%rcx),%rdi
    7d2d:	48 8d b4 11 80 00 00 00 	lea    0x80(%rcx,%rdx,1),%rsi
    7d35:	48 05 44 01 00 00    	add    $0x144,%rax
    7d3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    7d40:	48 89 fa             	mov    %rdi,%rdx
    7d43:	48 c1 ea 03          	shr    $0x3,%rdx
    7d47:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    7d4e:	84 d2                	test   %dl,%dl
    7d50:	74 09                	je     7d5b <barriered_reset+0x12b>
    7d52:	80 fa 03             	cmp    $0x3,%dl
    7d55:	0f 8e 81 00 00 00    	jle    7ddc <barriered_reset+0x1ac>
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    7d5b:	48 8d 8f 80 00 00 00 	lea    0x80(%rdi),%rcx
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    7d62:	83 07 01             	addl   $0x1,(%rdi)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    7d65:	48 89 ca             	mov    %rcx,%rdx
    7d68:	48 c1 ea 03          	shr    $0x3,%rdx
    7d6c:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    7d73:	84 d2                	test   %dl,%dl
    7d75:	74 05                	je     7d7c <barriered_reset+0x14c>
    7d77:	80 fa 03             	cmp    $0x3,%dl
    7d7a:	7e 58                	jle    7dd4 <barriered_reset+0x1a4>
      data->thread->tasks[x].available = 1; 
    7d7c:	48 89 c2             	mov    %rax,%rdx
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    7d7f:	83 87 80 00 00 00 01 	addl   $0x1,0x80(%rdi)
      data->thread->tasks[x].available = 1; 
    7d86:	48 c1 ea 03          	shr    $0x3,%rdx
    7d8a:	0f b6 8a 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%ecx
    7d91:	48 89 c2             	mov    %rax,%rdx
    7d94:	83 e2 07             	and    $0x7,%edx
    7d97:	83 c2 03             	add    $0x3,%edx
    7d9a:	38 ca                	cmp    %cl,%dl
    7d9c:	7c 04                	jl     7da2 <barriered_reset+0x172>
    7d9e:	84 c9                	test   %cl,%cl
    7da0:	75 2a                	jne    7dcc <barriered_reset+0x19c>
    for (int x = 0 ; x < data->task_count ; x++) {
    7da2:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
      data->thread->tasks[x].available = 1; 
    7da9:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    for (int x = 0 ; x < data->task_count ; x++) {
    7daf:	48 05 00 02 00 00    	add    $0x200,%rax
    7db5:	48 39 f7             	cmp    %rsi,%rdi
    7db8:	75 86                	jne    7d40 <barriered_reset+0x110>
  asm volatile ("sfence" ::: "memory");
    7dba:	0f ae f8             	sfence
}
    7dbd:	31 c0                	xor    %eax,%eax
    7dbf:	48 83 c4 08          	add    $0x8,%rsp
    7dc3:	c3                   	ret
    for (int x = 0 ; x < data->task_count ; x++) {
    7dc4:	48 89 d7             	mov    %rdx,%rdi
    7dc7:	e8 84 c7 ff ff       	call   4550 <__asan_report_load4@plt>
      data->thread->tasks[x].available = 1; 
    7dcc:	48 89 c7             	mov    %rax,%rdi
    7dcf:	e8 ec c8 ff ff       	call   46c0 <__asan_report_store4@plt>
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    7dd4:	48 89 cf             	mov    %rcx,%rdi
    7dd7:	e8 74 c7 ff ff       	call   4550 <__asan_report_load4@plt>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    7ddc:	e8 6f c7 ff ff       	call   4550 <__asan_report_load4@plt>
    7de1:	48 89 cf             	mov    %rcx,%rdi
    7de4:	e8 f7 c6 ff ff       	call   44e0 <__asan_report_load8@plt>
    7de9:	48 89 f7             	mov    %rsi,%rdi
    7dec:	e8 5f c7 ff ff       	call   4550 <__asan_report_load4@plt>
    7df1:	48 89 c7             	mov    %rax,%rdi
    7df4:	e8 e7 c6 ff ff       	call   44e0 <__asan_report_load8@plt>
    7df9:	e8 e2 c6 ff ff       	call   44e0 <__asan_report_load8@plt>
    7dfe:	e8 dd c6 ff ff       	call   44e0 <__asan_report_load8@plt>
      data->thread->tasks[x].available = 1; 
    7e03:	e8 d8 c6 ff ff       	call   44e0 <__asan_report_load8@plt>
    7e08:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000007e10 <external_thread>:
void * external_thread(void *arg) {
    7e10:	f3 0f 1e fa          	endbr64
    7e14:	41 57                	push   %r15
    7e16:	41 56                	push   %r14
    7e18:	49 89 fe             	mov    %rdi,%r14
  while (data->running == 1) {
    7e1b:	48 83 c7 44          	add    $0x44,%rdi
void * external_thread(void *arg) {
    7e1f:	41 55                	push   %r13
  while (data->running == 1) {
    7e21:	48 89 f8             	mov    %rdi,%rax
void * external_thread(void *arg) {
    7e24:	41 54                	push   %r12
  while (data->running == 1) {
    7e26:	48 c1 e8 03          	shr    $0x3,%rax
void * external_thread(void *arg) {
    7e2a:	55                   	push   %rbp
    7e2b:	53                   	push   %rbx
    7e2c:	48 83 ec 08          	sub    $0x8,%rsp
  while (data->running == 1) {
    7e30:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    7e37:	48 89 f8             	mov    %rdi,%rax
    7e3a:	83 e0 07             	and    $0x7,%eax
    7e3d:	83 c0 03             	add    $0x3,%eax
    7e40:	38 d0                	cmp    %dl,%al
    7e42:	7c 08                	jl     7e4c <external_thread+0x3c>
    7e44:	84 d2                	test   %dl,%dl
    7e46:	0f 85 4d 03 00 00    	jne    8199 <external_thread+0x389>
    7e4c:	41 83 7e 44 01       	cmpl   $0x1,0x44(%r14)
    7e51:	0f 85 27 01 00 00    	jne    7f7e <external_thread+0x16e>
    for (int b = 0; b < data->buffers_count; b++) {
    7e57:	49 8d be bc 00 00 00 	lea    0xbc(%r14),%rdi
    7e5e:	48 89 f8             	mov    %rdi,%rax
    7e61:	48 c1 e8 03          	shr    $0x3,%rax
    7e65:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    7e6c:	48 89 f8             	mov    %rdi,%rax
    7e6f:	83 e0 07             	and    $0x7,%eax
    7e72:	83 c0 03             	add    $0x3,%eax
    7e75:	38 d0                	cmp    %dl,%al
    7e77:	7c 08                	jl     7e81 <external_thread+0x71>
    7e79:	84 d2                	test   %dl,%dl
    7e7b:	0f 85 0b 03 00 00    	jne    818c <external_thread+0x37c>
    7e81:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    7e88:	4d 8d 6e 50          	lea    0x50(%r14),%r13
    7e8c:	0f 1f 40 00          	nopl   0x0(%rax)
    7e90:	85 f6                	test   %esi,%esi
    7e92:	0f 8e f7 00 00 00    	jle    7f8f <external_thread+0x17f>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    7e98:	4c 89 e8             	mov    %r13,%rax
    7e9b:	48 c1 e8 03          	shr    $0x3,%rax
    7e9f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    7ea6:	0f 85 e5 02 00 00    	jne    8191 <external_thread+0x381>
    7eac:	4d 8b 5e 50          	mov    0x50(%r14),%r11
    7eb0:	45 31 e4             	xor    %r12d,%r12d
    7eb3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7eb8:	4e 8d 3c e5 00 00 00 00 	lea    0x0(,%r12,8),%r15
    7ec0:	4b 8d 0c 3b          	lea    (%r11,%r15,1),%rcx
    7ec4:	48 89 c8             	mov    %rcx,%rax
    7ec7:	48 c1 e8 03          	shr    $0x3,%rax
    7ecb:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    7ed2:	0f 85 ac 02 00 00    	jne    8184 <external_thread+0x374>
    7ed8:	48 8b 01             	mov    (%rcx),%rax
    7edb:	48 89 c2             	mov    %rax,%rdx
    7ede:	48 c1 ea 03          	shr    $0x3,%rdx
    7ee2:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    7ee9:	84 d2                	test   %dl,%dl
    7eeb:	74 09                	je     7ef6 <external_thread+0xe6>
    7eed:	80 fa 03             	cmp    $0x3,%dl
    7ef0:	0f 8e 86 02 00 00    	jle    817c <external_thread+0x36c>
    7ef6:	44 8b 08             	mov    (%rax),%r9d
    7ef9:	31 db                	xor    %ebx,%ebx
    7efb:	4c 8d 50 08          	lea    0x8(%rax),%r10
    7eff:	45 85 c9             	test   %r9d,%r9d
    7f02:	7e 62                	jle    7f66 <external_thread+0x156>
    7f04:	0f 1f 40 00          	nopl   0x0(%rax)
				if (data->buffers[b]->buffer[x].available == 0) {
    7f08:	4c 89 d2             	mov    %r10,%rdx
    7f0b:	48 c1 ea 03          	shr    $0x3,%rdx
    7f0f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    7f16:	0f 85 0d 02 00 00    	jne    8129 <external_thread+0x319>
    7f1c:	48 8b 78 08          	mov    0x8(%rax),%rdi
    7f20:	48 89 dd             	mov    %rbx,%rbp
    7f23:	48 c1 e5 08          	shl    $0x8,%rbp
    7f27:	48 01 ef             	add    %rbp,%rdi
    7f2a:	48 8d b7 80 00 00 00 	lea    0x80(%rdi),%rsi
    7f31:	48 89 f2             	mov    %rsi,%rdx
    7f34:	48 c1 ea 03          	shr    $0x3,%rdx
    7f38:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    7f3f:	84 d2                	test   %dl,%dl
    7f41:	74 09                	je     7f4c <external_thread+0x13c>
    7f43:	80 fa 03             	cmp    $0x3,%dl
    7f46:	0f 8e e5 01 00 00    	jle    8131 <external_thread+0x321>
    7f4c:	8b 97 80 00 00 00    	mov    0x80(%rdi),%edx
    7f52:	85 d2                	test   %edx,%edx
    7f54:	74 42                	je     7f98 <external_thread+0x188>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    7f56:	48 83 c3 01          	add    $0x1,%rbx
    7f5a:	41 39 d9             	cmp    %ebx,%r9d
    7f5d:	7f a9                	jg     7f08 <external_thread+0xf8>
    for (int b = 0; b < data->buffers_count; b++) {
    7f5f:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    7f66:	49 83 c4 01          	add    $0x1,%r12
    7f6a:	44 39 e6             	cmp    %r12d,%esi
    7f6d:	0f 8f 45 ff ff ff    	jg     7eb8 <external_thread+0xa8>
  while (data->running == 1) {
    7f73:	41 83 7e 44 01       	cmpl   $0x1,0x44(%r14)
    7f78:	0f 84 12 ff ff ff    	je     7e90 <external_thread+0x80>
}
    7f7e:	48 83 c4 08          	add    $0x8,%rsp
    7f82:	31 c0                	xor    %eax,%eax
    7f84:	5b                   	pop    %rbx
    7f85:	5d                   	pop    %rbp
    7f86:	41 5c                	pop    %r12
    7f88:	41 5d                	pop    %r13
    7f8a:	41 5e                	pop    %r14
    7f8c:	41 5f                	pop    %r15
    7f8e:	c3                   	ret
  while (data->running == 1) {
    7f8f:	eb fe                	jmp    7f8f <external_thread+0x17f>
    7f91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    7f98:	48 89 f8             	mov    %rdi,%rax
    7f9b:	48 c1 e8 03          	shr    $0x3,%rax
    7f9f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    7fa6:	0f 85 cb 01 00 00    	jne    8177 <external_thread+0x367>
    7fac:	48 8d 05 6d 90 00 00 	lea    0x906d(%rip),%rax        # 11020 <_IO_stdin_used+0x20>
    7fb3:	48 89 07             	mov    %rax,(%rdi)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    7fb6:	48 89 c8             	mov    %rcx,%rax
    7fb9:	48 c1 e8 03          	shr    $0x3,%rax
    7fbd:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    7fc4:	0f 85 a0 01 00 00    	jne    816a <external_thread+0x35a>
    7fca:	48 8b 01             	mov    (%rcx),%rax
    7fcd:	48 8d 78 08          	lea    0x8(%rax),%rdi
    7fd1:	48 89 fa             	mov    %rdi,%rdx
    7fd4:	48 c1 ea 03          	shr    $0x3,%rdx
    7fd8:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    7fdf:	0f 85 8d 01 00 00    	jne    8172 <external_thread+0x362>
    7fe5:	48 8b 48 08          	mov    0x8(%rax),%rcx
    7fe9:	48 01 e9             	add    %rbp,%rcx
    7fec:	48 8d b9 88 00 00 00 	lea    0x88(%rcx),%rdi
    7ff3:	48 89 c8             	mov    %rcx,%rax
    7ff6:	48 89 fa             	mov    %rdi,%rdx
    7ff9:	48 c1 ea 03          	shr    $0x3,%rdx
    7ffd:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    8004:	0f 85 2f 01 00 00    	jne    8139 <external_thread+0x329>
    800a:	48 8d b9 94 00 00 00 	lea    0x94(%rcx),%rdi
    8011:	48 8b b1 88 00 00 00 	mov    0x88(%rcx),%rsi
    8018:	48 89 fa             	mov    %rdi,%rdx
    801b:	48 c1 ea 03          	shr    $0x3,%rdx
    801f:	0f b6 8a 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%ecx
    8026:	48 89 fa             	mov    %rdi,%rdx
    8029:	83 e2 07             	and    $0x7,%edx
    802c:	83 c2 03             	add    $0x3,%edx
    802f:	38 ca                	cmp    %cl,%dl
    8031:	7c 08                	jl     803b <external_thread+0x22b>
    8033:	84 c9                	test   %cl,%cl
    8035:	0f 85 03 01 00 00    	jne    813e <external_thread+0x32e>
    803b:	48 63 80 94 00 00 00 	movslq 0x94(%rax),%rax
    8042:	bf 04 00 00 00       	mov    $0x4,%edi
    8047:	48 c1 e0 05          	shl    $0x5,%rax
    804b:	48 01 c6             	add    %rax,%rsi
    804e:	e8 2d c4 ff ff       	call   4480 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    8053:	4c 89 e8             	mov    %r13,%rax
    8056:	48 c1 e8 03          	shr    $0x3,%rax
    805a:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    8061:	0f 85 dc 00 00 00    	jne    8143 <external_thread+0x333>
    8067:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    806b:	4c 01 ff             	add    %r15,%rdi
    806e:	48 89 f8             	mov    %rdi,%rax
    8071:	48 c1 e8 03          	shr    $0x3,%rax
    8075:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    807c:	0f 85 c9 00 00 00    	jne    814b <external_thread+0x33b>
    8082:	48 8b 07             	mov    (%rdi),%rax
    8085:	48 8d 78 08          	lea    0x8(%rax),%rdi
    8089:	48 89 fa             	mov    %rdi,%rdx
    808c:	48 c1 ea 03          	shr    $0x3,%rdx
    8090:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    8097:	0f 85 b3 00 00 00    	jne    8150 <external_thread+0x340>
    809d:	48 03 68 08          	add    0x8(%rax),%rbp
    80a1:	48 8d bd 80 00 00 00 	lea    0x80(%rbp),%rdi
    80a8:	48 89 f8             	mov    %rdi,%rax
    80ab:	48 c1 e8 03          	shr    $0x3,%rax
    80af:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    80b6:	84 c0                	test   %al,%al
    80b8:	74 08                	je     80c2 <external_thread+0x2b2>
    80ba:	3c 03                	cmp    $0x3,%al
    80bc:	0f 8e 93 00 00 00    	jle    8155 <external_thread+0x345>
    80c2:	c7 85 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rbp)
          asm volatile ("sfence" ::: "memory");
    80cc:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    80cf:	4d 8b 5e 50          	mov    0x50(%r14),%r11
    80d3:	4b 8d 0c 3b          	lea    (%r11,%r15,1),%rcx
    80d7:	48 89 c8             	mov    %rcx,%rax
    80da:	48 c1 e8 03          	shr    $0x3,%rax
    80de:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    80e5:	75 73                	jne    815a <external_thread+0x34a>
    80e7:	48 8b 01             	mov    (%rcx),%rax
    80ea:	48 89 c2             	mov    %rax,%rdx
    80ed:	48 c1 ea 03          	shr    $0x3,%rdx
    80f1:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    80f8:	84 d2                	test   %dl,%dl
    80fa:	74 05                	je     8101 <external_thread+0x2f1>
    80fc:	80 fa 03             	cmp    $0x3,%dl
    80ff:	7e 61                	jle    8162 <external_thread+0x352>
    8101:	44 8b 08             	mov    (%rax),%r9d
    8104:	48 83 c3 01          	add    $0x1,%rbx
    8108:	41 39 d9             	cmp    %ebx,%r9d
    810b:	0f 8e 4e fe ff ff    	jle    7f5f <external_thread+0x14f>
    8111:	4c 8d 50 08          	lea    0x8(%rax),%r10
				if (data->buffers[b]->buffer[x].available == 0) {
    8115:	4c 89 d2             	mov    %r10,%rdx
    8118:	48 c1 ea 03          	shr    $0x3,%rdx
    811c:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    8123:	0f 84 f3 fd ff ff    	je     7f1c <external_thread+0x10c>
    8129:	4c 89 d7             	mov    %r10,%rdi
    812c:	e8 af c3 ff ff       	call   44e0 <__asan_report_load8@plt>
    8131:	48 89 f7             	mov    %rsi,%rdi
    8134:	e8 17 c4 ff ff       	call   4550 <__asan_report_load4@plt>
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    8139:	e8 a2 c3 ff ff       	call   44e0 <__asan_report_load8@plt>
    813e:	e8 0d c4 ff ff       	call   4550 <__asan_report_load4@plt>
					data->buffers[b]->buffer[x].available = 1;
    8143:	4c 89 ef             	mov    %r13,%rdi
    8146:	e8 95 c3 ff ff       	call   44e0 <__asan_report_load8@plt>
    814b:	e8 90 c3 ff ff       	call   44e0 <__asan_report_load8@plt>
    8150:	e8 8b c3 ff ff       	call   44e0 <__asan_report_load8@plt>
    8155:	e8 66 c5 ff ff       	call   46c0 <__asan_report_store4@plt>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    815a:	48 89 cf             	mov    %rcx,%rdi
    815d:	e8 7e c3 ff ff       	call   44e0 <__asan_report_load8@plt>
    8162:	48 89 c7             	mov    %rax,%rdi
    8165:	e8 e6 c3 ff ff       	call   4550 <__asan_report_load4@plt>
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    816a:	48 89 cf             	mov    %rcx,%rdi
    816d:	e8 6e c3 ff ff       	call   44e0 <__asan_report_load8@plt>
    8172:	e8 69 c3 ff ff       	call   44e0 <__asan_report_load8@plt>
					data->buffers[b]->buffer[x].data = "Hello world";
    8177:	e8 54 c5 ff ff       	call   46d0 <__asan_report_store8@plt>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    817c:	48 89 c7             	mov    %rax,%rdi
    817f:	e8 cc c3 ff ff       	call   4550 <__asan_report_load4@plt>
    8184:	48 89 cf             	mov    %rcx,%rdi
    8187:	e8 54 c3 ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int b = 0; b < data->buffers_count; b++) {
    818c:	e8 bf c3 ff ff       	call   4550 <__asan_report_load4@plt>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    8191:	4c 89 ef             	mov    %r13,%rdi
    8194:	e8 47 c3 ff ff       	call   44e0 <__asan_report_load8@plt>
  while (data->running == 1) {
    8199:	e8 b2 c3 ff ff       	call   4550 <__asan_report_load4@plt>
    819e:	66 90                	xchg   %ax,%ax

00000000000081a0 <timer_thread>:
void* timer_thread(void *arg) {
    81a0:	f3 0f 1e fa          	endbr64
    81a4:	41 57                	push   %r15
    81a6:	49 89 ff             	mov    %rdi,%r15
    81a9:	41 56                	push   %r14
    81ab:	41 55                	push   %r13
    81ad:	41 54                	push   %r12
    81af:	55                   	push   %rbp
    81b0:	53                   	push   %rbx
    81b1:	48 81 ec 38 01 00 00 	sub    $0x138,%rsp
    81b8:	44 8b 05 41 e9 00 00 	mov    0xe941(%rip),%r8d        # 16b00 <__asan_option_detect_stack_use_after_return@@Base>
    81bf:	48 8d 44 24 70       	lea    0x70(%rsp),%rax
    81c4:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    81c9:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    81ce:	45 85 c0             	test   %r8d,%r8d
    81d1:	0f 85 03 0d 00 00    	jne    8eda <timer_thread+0xd3a>
    81d7:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    81dc:	48 8d 1d 7d ac 00 00 	lea    0xac7d(%rip),%rbx        # 12e60 <_IO_stdin_used+0x1e60>
  printf("In timer task %d\n", data->thread_index);
    81e3:	49 8d 7f 04          	lea    0x4(%r15),%rdi
void* timer_thread(void *arg) {
    81e7:	48 89 58 08          	mov    %rbx,0x8(%rax)
    81eb:	48 8d 1d ae ff ff ff 	lea    -0x52(%rip),%rbx        # 81a0 <timer_thread>
    81f2:	4c 8d a0 c0 00 00 00 	lea    0xc0(%rax),%r12
    81f9:	48 c7 00 b3 8a b5 41 	movq   $0x41b58ab3,(%rax)
    8200:	48 89 58 10          	mov    %rbx,0x10(%rax)
    8204:	48 c1 e8 03          	shr    $0x3,%rax
    8208:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    820d:	c7 80 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%rax)
    8217:	c7 80 04 80 ff 7f 00 00 f2 f2 	movl   $0xf2f20000,0x7fff8004(%rax)
    8221:	c7 80 08 80 ff 7f 00 00 f2 f2 	movl   $0xf2f20000,0x7fff8008(%rax)
    822b:	c7 80 0c 80 ff 7f 00 00 f2 f2 	movl   $0xf2f20000,0x7fff800c(%rax)
    8235:	c7 80 10 80 ff 7f 00 00 f3 f3 	movl   $0xf3f30000,0x7fff8010(%rax)
    823f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    8248:	48 89 84 24 28 01 00 00 	mov    %rax,0x128(%rsp)
    8250:	31 c0                	xor    %eax,%eax
  printf("In timer task %d\n", data->thread_index);
    8252:	48 89 f8             	mov    %rdi,%rax
    8255:	48 c1 e8 03          	shr    $0x3,%rax
    8259:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    8260:	48 89 f8             	mov    %rdi,%rax
    8263:	83 e0 07             	and    $0x7,%eax
    8266:	83 c0 03             	add    $0x3,%eax
    8269:	38 d0                	cmp    %dl,%al
    826b:	7c 08                	jl     8275 <timer_thread+0xd5>
    826d:	84 d2                	test   %dl,%dl
    826f:	0f 85 60 0c 00 00    	jne    8ed5 <timer_thread+0xd35>
    8275:	41 8b 57 04          	mov    0x4(%r15),%edx
    8279:	31 c0                	xor    %eax,%eax
    827b:	bf 01 00 00 00       	mov    $0x1,%edi
    8280:	48 8d 35 d9 8d 00 00 	lea    0x8dd9(%rip),%rsi        # 11060 <_IO_stdin_used+0x60>
    8287:	e8 94 c2 ff ff       	call   4520 <__printf_chk@plt>
  struct timespec preempt = {
    828c:	49 8d 44 24 80       	lea    -0x80(%r12),%rax
    8291:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    8296:	48 c1 e8 03          	shr    $0x3,%rax
    829a:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    82a1:	0f 85 24 0c 00 00    	jne    8ecb <timer_thread+0xd2b>
    82a7:	49 c7 44 24 80 00 00 00 00 	movq   $0x0,-0x80(%r12)
    82b0:	49 8d 7c 24 88       	lea    -0x78(%r12),%rdi
    82b5:	48 89 f8             	mov    %rdi,%rax
    82b8:	48 c1 e8 03          	shr    $0x3,%rax
    82bc:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    82c3:	0f 85 fd 0b 00 00    	jne    8ec6 <timer_thread+0xd26>
  while (data->running && n < times) {
    82c9:	49 8d 5f 44          	lea    0x44(%r15),%rbx
    82cd:	ba 88 13 00 00       	mov    $0x1388,%edx
    82d2:	bf 01 00 00 00       	mov    $0x1,%edi
    82d7:	31 c0                	xor    %eax,%eax
  struct timespec preempt = {
    82d9:	49 c7 44 24 88 40 42 0f 00 	movq   $0xf4240,-0x78(%r12)
    82e2:	48 8d 35 b7 8d 00 00 	lea    0x8db7(%rip),%rsi        # 110a0 <_IO_stdin_used+0xa0>
    82e9:	e8 32 c2 ff ff       	call   4520 <__printf_chk@plt>
  while (data->running && n < times) {
    82ee:	48 89 d8             	mov    %rbx,%rax
    82f1:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
    82f6:	48 c1 e8 03          	shr    $0x3,%rax
    82fa:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    8301:	48 89 d8             	mov    %rbx,%rax
    8304:	83 e0 07             	and    $0x7,%eax
    8307:	83 c0 03             	add    $0x3,%eax
    830a:	38 d0                	cmp    %dl,%al
    830c:	7c 08                	jl     8316 <timer_thread+0x176>
    830e:	84 d2                	test   %dl,%dl
    8310:	0f 85 a8 0b 00 00    	jne    8ebe <timer_thread+0xd1e>
    8316:	41 8b 5f 44          	mov    0x44(%r15),%ebx
    831a:	85 db                	test   %ebx,%ebx
    831c:	0f 84 75 0b 00 00    	je     8e97 <timer_thread+0xcf7>
    8322:	49 8d 84 24 60 ff ff ff 	lea    -0xa0(%r12),%rax
        int next = (y + 1) % data->threads[x]->task_count;
    832a:	4d 8d 6f 18          	lea    0x18(%r15),%r13
  int n = 0;
    832e:	31 ed                	xor    %ebp,%ebp
  int y = 0;
    8330:	31 db                	xor    %ebx,%ebx
    8332:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    8337:	49 8d 47 30          	lea    0x30(%r15),%rax
    833b:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    8340:	48 c1 e8 03          	shr    $0x3,%rax
    8344:	49 89 c6             	mov    %rax,%r14
        int next = (y + 1) % data->threads[x]->task_count;
    8347:	4c 89 e8             	mov    %r13,%rax
    y++;
    834a:	4c 89 2c 24          	mov    %r13,(%rsp)
        int next = (y + 1) % data->threads[x]->task_count;
    834e:	48 c1 e8 03          	shr    $0x3,%rax
    y++;
    8352:	4c 89 64 24 30       	mov    %r12,0x30(%rsp)
    8357:	4c 8b 64 24 20       	mov    0x20(%rsp),%r12
        int next = (y + 1) % data->threads[x]->task_count;
    835c:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    8361:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    nanosleep(&preempt , &rem2);
    8368:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    836d:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    n++;
    8372:	83 c5 01             	add    $0x1,%ebp
    nanosleep(&preempt , &rem2);
    8375:	e8 66 c3 ff ff       	call   46e0 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    837a:	41 0f b6 86 00 80 ff 7f 	movzbl 0x7fff8000(%r14),%eax
    8382:	84 c0                	test   %al,%al
    8384:	74 08                	je     838e <timer_thread+0x1ee>
    8386:	3c 03                	cmp    $0x3,%al
    8388:	0f 8e 26 0b 00 00    	jle    8eb4 <timer_thread+0xd14>
    838e:	49 63 47 30          	movslq 0x30(%r15),%rax
    y++;
    8392:	44 8d 6b 01          	lea    0x1(%rbx),%r13d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    8396:	85 c0                	test   %eax,%eax
    8398:	0f 8e 01 01 00 00    	jle    849f <timer_thread+0x2ff>
        int next = (y + 1) % data->threads[x]->task_count;
    839e:	48 8b 4c 24 28       	mov    0x28(%rsp),%rcx
    83a3:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    83aa:	0f 85 10 0c 00 00    	jne    8fc0 <timer_thread+0xe20>
    83b0:	49 8b 7f 18          	mov    0x18(%r15),%rdi
        data->threads[x]->tasks[y].scheduled = 0;
    83b4:	4c 63 cb             	movslq %ebx,%r9
    83b7:	49 c1 e1 09          	shl    $0x9,%r9
    83bb:	4c 8d 14 c7          	lea    (%rdi,%rax,8),%r10
    83bf:	90                   	nop
        int next = (y + 1) % data->threads[x]->task_count;
    83c0:	48 89 f8             	mov    %rdi,%rax
    83c3:	48 c1 e8 03          	shr    $0x3,%rax
    83c7:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    83ce:	0f 85 9e 0a 00 00    	jne    8e72 <timer_thread+0xcd2>
    83d4:	48 8b 0f             	mov    (%rdi),%rcx
    83d7:	48 8d 51 40          	lea    0x40(%rcx),%rdx
    83db:	48 89 d0             	mov    %rdx,%rax
    83de:	48 c1 e8 03          	shr    $0x3,%rax
    83e2:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    83e9:	84 c0                	test   %al,%al
    83eb:	74 08                	je     83f5 <timer_thread+0x255>
    83ed:	3c 03                	cmp    $0x3,%al
    83ef:	0f 8e 82 0a 00 00    	jle    8e77 <timer_thread+0xcd7>
    83f5:	44 89 e8             	mov    %r13d,%eax
    83f8:	99                   	cltd
    83f9:	f7 79 40             	idivl  0x40(%rcx)
        data->threads[x]->tasks[next].scheduled = 1;
    83fc:	48 8d 41 38          	lea    0x38(%rcx),%rax
    8400:	48 89 c6             	mov    %rax,%rsi
    8403:	48 c1 ee 03          	shr    $0x3,%rsi
    8407:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    840e:	0f 85 6b 0a 00 00    	jne    8e7f <timer_thread+0xcdf>
    8414:	48 8b 49 38          	mov    0x38(%rcx),%rcx
    8418:	48 63 d2             	movslq %edx,%rdx
    841b:	48 c1 e2 09          	shl    $0x9,%rdx
    841f:	48 8d 04 11          	lea    (%rcx,%rdx,1),%rax
    8423:	4c 8d 80 4c 01 00 00 	lea    0x14c(%rax),%r8
    842a:	4c 89 c2             	mov    %r8,%rdx
    842d:	48 c1 ea 03          	shr    $0x3,%rdx
    8431:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    8438:	4c 89 c2             	mov    %r8,%rdx
    843b:	83 e2 07             	and    $0x7,%edx
    843e:	83 c2 03             	add    $0x3,%edx
    8441:	40 38 f2             	cmp    %sil,%dl
    8444:	7c 09                	jl     844f <timer_thread+0x2af>
    8446:	40 84 f6             	test   %sil,%sil
    8449:	0f 85 38 0a 00 00    	jne    8e87 <timer_thread+0xce7>
    844f:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    8459:	4c 01 c9             	add    %r9,%rcx
    845c:	48 8d 91 4c 01 00 00 	lea    0x14c(%rcx),%rdx
    8463:	48 89 d0             	mov    %rdx,%rax
    8466:	48 c1 e8 03          	shr    $0x3,%rax
    846a:	0f b6 b0 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%esi
    8471:	48 89 d0             	mov    %rdx,%rax
    8474:	83 e0 07             	and    $0x7,%eax
    8477:	83 c0 03             	add    $0x3,%eax
    847a:	40 38 f0             	cmp    %sil,%al
    847d:	7c 09                	jl     8488 <timer_thread+0x2e8>
    847f:	40 84 f6             	test   %sil,%sil
    8482:	0f 85 07 0a 00 00    	jne    8e8f <timer_thread+0xcef>
    8488:	c7 81 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rcx)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    8492:	48 83 c7 08          	add    $0x8,%rdi
    8496:	4c 39 d7             	cmp    %r10,%rdi
    8499:	0f 85 21 ff ff ff    	jne    83c0 <timer_thread+0x220>
    asm volatile ("mfence" ::: "memory");
    849f:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    84a2:	48 8b 04 24          	mov    (%rsp),%rax
    84a6:	48 c1 e8 03          	shr    $0x3,%rax
    84aa:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    84b1:	0f 85 4e 0a 00 00    	jne    8f05 <timer_thread+0xd65>
    84b7:	49 8b 7f 18          	mov    0x18(%r15),%rdi
    84bb:	48 89 f8             	mov    %rdi,%rax
    84be:	48 c1 e8 03          	shr    $0x3,%rax
    84c2:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    84c9:	0f 85 31 0a 00 00    	jne    8f00 <timer_thread+0xd60>
    84cf:	48 8b 07             	mov    (%rdi),%rax
    84d2:	48 8d 78 40          	lea    0x40(%rax),%rdi
    84d6:	48 89 fa             	mov    %rdi,%rdx
    84d9:	48 c1 ea 03          	shr    $0x3,%rdx
    84dd:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    84e4:	84 d2                	test   %dl,%dl
    84e6:	74 09                	je     84f1 <timer_thread+0x351>
    84e8:	80 fa 03             	cmp    $0x3,%dl
    84eb:	0f 8e 8f 0a 00 00    	jle    8f80 <timer_thread+0xde0>
    y++;
    84f1:	31 db                	xor    %ebx,%ebx
    84f3:	44 39 68 40          	cmp    %r13d,0x40(%rax)
  while (data->running && n < times) {
    84f7:	4c 89 e0             	mov    %r12,%rax
    y++;
    84fa:	41 0f 4f dd          	cmovg  %r13d,%ebx
  while (data->running && n < times) {
    84fe:	48 c1 e8 03          	shr    $0x3,%rax
    8502:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    8509:	4c 89 e0             	mov    %r12,%rax
    850c:	83 e0 07             	and    $0x7,%eax
    850f:	83 c0 03             	add    $0x3,%eax
    8512:	38 c8                	cmp    %cl,%al
    8514:	7c 08                	jl     851e <timer_thread+0x37e>
    8516:	84 c9                	test   %cl,%cl
    8518:	0f 85 8b 0a 00 00    	jne    8fa9 <timer_thread+0xe09>
    851e:	41 8b 7f 44          	mov    0x44(%r15),%edi
    8522:	85 ff                	test   %edi,%edi
    8524:	74 0c                	je     8532 <timer_thread+0x392>
    8526:	81 fd 88 13 00 00    	cmp    $0x1388,%ebp
    852c:	0f 85 36 fe ff ff    	jne    8368 <timer_thread+0x1c8>
    8532:	4c 8b 64 24 30       	mov    0x30(%rsp),%r12
    8537:	48 8d 3d a2 8b 00 00 	lea    0x8ba2(%rip),%rdi        # 110e0 <_IO_stdin_used+0xe0>
    853e:	e8 bd c2 ff ff       	call   4800 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    8543:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    8548:	48 c1 e8 03          	shr    $0x3,%rax
    854c:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    8553:	84 c0                	test   %al,%al
    8555:	74 08                	je     855f <timer_thread+0x3bf>
    8557:	3c 03                	cmp    $0x3,%al
    8559:	0f 8e b9 09 00 00    	jle    8f18 <timer_thread+0xd78>
    855f:	49 63 47 30          	movslq 0x30(%r15),%rax
    8563:	85 c0                	test   %eax,%eax
    8565:	0f 8e df 00 00 00    	jle    864a <timer_thread+0x4aa>
    for (int y = 0 ; y < data->task_count ; y++) {
    856b:	49 8d 7f 40          	lea    0x40(%r15),%rdi
    856f:	48 89 fa             	mov    %rdi,%rdx
    8572:	48 c1 ea 03          	shr    $0x3,%rdx
    8576:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    857d:	84 d2                	test   %dl,%dl
    857f:	74 09                	je     858a <timer_thread+0x3ea>
    8581:	80 fa 03             	cmp    $0x3,%dl
    8584:	0f 8e 31 0a 00 00    	jle    8fbb <timer_thread+0xe1b>
    858a:	4d 63 47 40          	movslq 0x40(%r15),%r8
    858e:	48 8d 34 c5 00 00 00 00 	lea    0x0(,%rax,8),%rsi
    8596:	31 c9                	xor    %ecx,%ecx
    8598:	4c 89 c2             	mov    %r8,%rdx
    859b:	49 c1 e0 09          	shl    $0x9,%r8
    859f:	85 d2                	test   %edx,%edx
    85a1:	0f 8e 85 08 00 00    	jle    8e2c <timer_thread+0xc8c>
    85a7:	49 8d 47 18          	lea    0x18(%r15),%rax
    85ab:	49 81 c0 80 01 00 00 	add    $0x180,%r8
      data->threads[x]->tasks[y].sending = 0;
    85b2:	49 89 c1             	mov    %rax,%r9
    85b5:	49 c1 e9 03          	shr    $0x3,%r9
    85b9:	41 80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r9)
    85c1:	0f 85 ec 09 00 00    	jne    8fb3 <timer_thread+0xe13>
    85c7:	49 8b 7f 18          	mov    0x18(%r15),%rdi
    85cb:	48 01 cf             	add    %rcx,%rdi
    85ce:	48 89 fa             	mov    %rdi,%rdx
    85d1:	48 c1 ea 03          	shr    $0x3,%rdx
    85d5:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    85dc:	0f 85 c3 08 00 00    	jne    8ea5 <timer_thread+0xd05>
    85e2:	48 8b 17             	mov    (%rdi),%rdx
    85e5:	48 8d 7a 38          	lea    0x38(%rdx),%rdi
    85e9:	49 89 fa             	mov    %rdi,%r10
    85ec:	49 c1 ea 03          	shr    $0x3,%r10
    85f0:	41 80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r10)
    85f8:	0f 85 5f 0a 00 00    	jne    905d <timer_thread+0xebd>
    85fe:	4c 8b 52 38          	mov    0x38(%rdx),%r10
    8602:	49 8d ba 80 01 00 00 	lea    0x180(%r10),%rdi
    8609:	4d 01 c2             	add    %r8,%r10
    860c:	0f 1f 40 00          	nopl   0x0(%rax)
    8610:	48 89 fa             	mov    %rdi,%rdx
    8613:	48 c1 ea 03          	shr    $0x3,%rdx
    8617:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    861e:	84 d2                	test   %dl,%dl
    8620:	74 09                	je     862b <timer_thread+0x48b>
    8622:	80 fa 03             	cmp    $0x3,%dl
    8625:	0f 8e 2d 0a 00 00    	jle    9058 <timer_thread+0xeb8>
    862b:	c7 07 00 00 00 00    	movl   $0x0,(%rdi)
    for (int y = 0 ; y < data->task_count ; y++) {
    8631:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    8638:	4c 39 d7             	cmp    %r10,%rdi
    863b:	75 d3                	jne    8610 <timer_thread+0x470>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    863d:	48 83 c1 08          	add    $0x8,%rcx
    8641:	48 39 f1             	cmp    %rsi,%rcx
    8644:	0f 85 6f ff ff ff    	jne    85b9 <timer_thread+0x419>
  asm volatile ("mfence" ::: "memory");
    864a:	0f ae f0             	mfence
  struct timespec drain = {
    864d:	49 8d 44 24 c0       	lea    -0x40(%r12),%rax
    8652:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    8657:	48 c1 e8 03          	shr    $0x3,%rax
    865b:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    8662:	0f 85 e1 09 00 00    	jne    9049 <timer_thread+0xea9>
    8668:	49 c7 44 24 c0 01 00 00 00 	movq   $0x1,-0x40(%r12)
    8671:	49 8d 7c 24 c8       	lea    -0x38(%r12),%rdi
    8676:	48 89 f8             	mov    %rdi,%rax
    8679:	48 c1 e8 03          	shr    $0x3,%rax
    867d:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    8684:	0f 85 ba 09 00 00    	jne    9044 <timer_thread+0xea4>
    868a:	49 8d 6f 28          	lea    0x28(%r15),%rbp
    868e:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    8693:	49 c7 44 24 c8 00 00 00 00 	movq   $0x0,-0x38(%r12)
    for (int x = 0 ; x < data->thread_count ; x++) {
    869c:	48 89 e8             	mov    %rbp,%rax
    869f:	48 89 6c 24 68       	mov    %rbp,0x68(%rsp)
    86a4:	89 dd                	mov    %ebx,%ebp
    86a6:	48 c1 e8 03          	shr    $0x3,%rax
    86aa:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    86af:	49 8d 47 18          	lea    0x18(%r15),%rax
    86b3:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
        int next = (y + 1) % data->threads[x]->task_count;
    86b8:	48 c1 e8 03          	shr    $0x3,%rax
    86bc:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    86c1:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    86c6:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    86cd:	84 c0                	test   %al,%al
    86cf:	74 08                	je     86d9 <timer_thread+0x539>
    86d1:	3c 03                	cmp    $0x3,%al
    86d3:	0f 8e 61 09 00 00    	jle    903a <timer_thread+0xe9a>
    86d9:	49 63 47 28          	movslq 0x28(%r15),%rax
    y++;
    86dd:	44 8d 5d 01          	lea    0x1(%rbp),%r11d
    for (int x = 0 ; x < data->thread_count ; x++) {
    86e1:	85 c0                	test   %eax,%eax
    86e3:	0f 8e 06 01 00 00    	jle    87ef <timer_thread+0x64f>
        int next = (y + 1) % data->threads[x]->task_count;
    86e9:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
    86ee:	80 bb 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rbx)
    86f5:	0f 85 35 09 00 00    	jne    9030 <timer_thread+0xe90>
    86fb:	49 8b 7f 18          	mov    0x18(%r15),%rdi
        data->threads[x]->tasks[y].scheduled = 0;
    86ff:	4c 63 cd             	movslq %ebp,%r9
    8702:	49 c1 e1 09          	shl    $0x9,%r9
    8706:	4c 8d 14 c7          	lea    (%rdi,%rax,8),%r10
    870a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    8710:	48 89 f8             	mov    %rdi,%rax
    8713:	48 c1 e8 03          	shr    $0x3,%rax
    8717:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    871e:	0f 85 07 09 00 00    	jne    902b <timer_thread+0xe8b>
    8724:	48 8b 0f             	mov    (%rdi),%rcx
    8727:	48 8d 51 40          	lea    0x40(%rcx),%rdx
    872b:	48 89 d0             	mov    %rdx,%rax
    872e:	48 c1 e8 03          	shr    $0x3,%rax
    8732:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    8739:	84 c0                	test   %al,%al
    873b:	74 08                	je     8745 <timer_thread+0x5a5>
    873d:	3c 03                	cmp    $0x3,%al
    873f:	0f 8e de 08 00 00    	jle    9023 <timer_thread+0xe83>
    8745:	44 89 d8             	mov    %r11d,%eax
    8748:	99                   	cltd
    8749:	f7 79 40             	idivl  0x40(%rcx)
        data->threads[x]->tasks[next].scheduled = 1;
    874c:	48 8d 41 38          	lea    0x38(%rcx),%rax
    8750:	48 89 c6             	mov    %rax,%rsi
    8753:	48 c1 ee 03          	shr    $0x3,%rsi
    8757:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    875e:	0f 85 b7 08 00 00    	jne    901b <timer_thread+0xe7b>
    8764:	48 8b 49 38          	mov    0x38(%rcx),%rcx
    8768:	48 63 d2             	movslq %edx,%rdx
    876b:	48 c1 e2 09          	shl    $0x9,%rdx
    876f:	48 8d 04 11          	lea    (%rcx,%rdx,1),%rax
    8773:	4c 8d 80 4c 01 00 00 	lea    0x14c(%rax),%r8
    877a:	4c 89 c2             	mov    %r8,%rdx
    877d:	48 c1 ea 03          	shr    $0x3,%rdx
    8781:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    8788:	4c 89 c2             	mov    %r8,%rdx
    878b:	83 e2 07             	and    $0x7,%edx
    878e:	83 c2 03             	add    $0x3,%edx
    8791:	40 38 f2             	cmp    %sil,%dl
    8794:	7c 09                	jl     879f <timer_thread+0x5ff>
    8796:	40 84 f6             	test   %sil,%sil
    8799:	0f 85 74 08 00 00    	jne    9013 <timer_thread+0xe73>
    879f:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    87a9:	4c 01 c9             	add    %r9,%rcx
    87ac:	48 8d 91 4c 01 00 00 	lea    0x14c(%rcx),%rdx
    87b3:	48 89 d0             	mov    %rdx,%rax
    87b6:	48 c1 e8 03          	shr    $0x3,%rax
    87ba:	0f b6 b0 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%esi
    87c1:	48 89 d0             	mov    %rdx,%rax
    87c4:	83 e0 07             	and    $0x7,%eax
    87c7:	83 c0 03             	add    $0x3,%eax
    87ca:	40 38 f0             	cmp    %sil,%al
    87cd:	7c 09                	jl     87d8 <timer_thread+0x638>
    87cf:	40 84 f6             	test   %sil,%sil
    87d2:	0f 85 33 08 00 00    	jne    900b <timer_thread+0xe6b>
    87d8:	c7 81 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rcx)
    for (int x = 0 ; x < data->thread_count ; x++) {
    87e2:	48 83 c7 08          	add    $0x8,%rdi
    87e6:	49 39 fa             	cmp    %rdi,%r10
    87e9:	0f 85 21 ff ff ff    	jne    8710 <timer_thread+0x570>
    asm volatile ("mfence" ::: "memory");
    87ef:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    87f2:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    87f7:	48 c1 e8 03          	shr    $0x3,%rax
    87fb:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    8802:	0f 85 f9 07 00 00    	jne    9001 <timer_thread+0xe61>
    8808:	49 8b 7f 18          	mov    0x18(%r15),%rdi
    880c:	48 89 f8             	mov    %rdi,%rax
    880f:	48 c1 e8 03          	shr    $0x3,%rax
    8813:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    881a:	0f 85 dc 07 00 00    	jne    8ffc <timer_thread+0xe5c>
    8820:	48 8b 07             	mov    (%rdi),%rax
    8823:	48 8d 78 40          	lea    0x40(%rax),%rdi
    8827:	48 89 fa             	mov    %rdi,%rdx
    882a:	48 c1 ea 03          	shr    $0x3,%rdx
    882e:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    8835:	84 d2                	test   %dl,%dl
    8837:	74 09                	je     8842 <timer_thread+0x6a2>
    8839:	80 fa 03             	cmp    $0x3,%dl
    883c:	0f 8e b5 07 00 00    	jle    8ff7 <timer_thread+0xe57>
    y++;
    8842:	44 39 58 40          	cmp    %r11d,0x40(%rax)
    8846:	b8 00 00 00 00       	mov    $0x0,%eax
    884b:	41 0f 4f c3          	cmovg  %r11d,%eax
    884f:	89 c5                	mov    %eax,%ebp
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    8851:	4c 89 f0             	mov    %r14,%rax
    8854:	48 c1 e8 03          	shr    $0x3,%rax
    8858:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    885f:	84 c0                	test   %al,%al
    8861:	74 08                	je     886b <timer_thread+0x6cb>
    8863:	3c 03                	cmp    $0x3,%al
    8865:	0f 8e 34 07 00 00    	jle    8f9f <timer_thread+0xdff>
    886b:	45 8b 57 30          	mov    0x30(%r15),%r10d
    886f:	45 85 d2             	test   %r10d,%r10d
    8872:	0f 8e ef 01 00 00    	jle    8a67 <timer_thread+0x8c7>
    int all_empty = 1;
    8878:	c7 44 24 08 01 00 00 00 	movl   $0x1,0x8(%rsp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    8880:	45 31 ed             	xor    %r13d,%r13d
    int all_empty = 1;
    8883:	89 6c 24 28          	mov    %ebp,0x28(%rsp)
    8887:	4c 89 64 24 30       	mov    %r12,0x30(%rsp)
    888c:	0f 1f 40 00          	nopl   0x0(%rax)
      for (int y = 0 ; y < 2 ; y++) {
    8890:	31 db                	xor    %ebx,%ebx
    8892:	44 89 ed             	mov    %r13d,%ebp
    8895:	4e 8d 24 ed 00 00 00 00 	lea    0x0(,%r13,8),%r12
    889d:	89 d9                	mov    %ebx,%ecx
        for (int k = 0 ; k < data->my_thread_count; k++) {
    889f:	45 85 d2             	test   %r10d,%r10d
    88a2:	0f 8e 58 01 00 00    	jle    8a00 <timer_thread+0x860>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    88a8:	49 8b 77 18          	mov    0x18(%r15),%rsi
    88ac:	4c 01 e6             	add    %r12,%rsi
    88af:	49 89 f3             	mov    %rsi,%r11
    88b2:	49 c1 eb 03          	shr    $0x3,%r11
    88b6:	41 80 bb 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r11)
    88be:	0f 85 a1 05 00 00    	jne    8e65 <timer_thread+0xcc5>
    88c4:	48 8b 16             	mov    (%rsi),%rdx
    88c7:	48 8d 7a 38          	lea    0x38(%rdx),%rdi
    88cb:	48 89 f8             	mov    %rdi,%rax
    88ce:	48 c1 e8 03          	shr    $0x3,%rax
    88d2:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    88d9:	0f 85 8e 05 00 00    	jne    8e6d <timer_thread+0xccd>
    88df:	48 89 d8             	mov    %rbx,%rax
    88e2:	48 c1 e0 09          	shl    $0x9,%rax
    88e6:	48 03 42 38          	add    0x38(%rdx),%rax
    88ea:	48 8d b8 70 01 00 00 	lea    0x170(%rax),%rdi
    88f1:	48 89 fa             	mov    %rdi,%rdx
    88f4:	48 c1 ea 03          	shr    $0x3,%rdx
    88f8:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    88ff:	0f 85 5b 05 00 00    	jne    8e60 <timer_thread+0xcc0>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    8905:	48 89 34 24          	mov    %rsi,(%rsp)
    8909:	48 8b b8 70 01 00 00 	mov    0x170(%rax),%rdi
    8910:	45 31 c0             	xor    %r8d,%r8d
    8913:	eb 1d                	jmp    8932 <timer_thread+0x792>
    8915:	0f 1f 00             	nopl   (%rax)
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    8918:	48 85 c0             	test   %rax,%rax
    891b:	0f 8f 85 00 00 00    	jg     89a6 <timer_thread+0x806>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    8921:	41 83 c0 01          	add    $0x1,%r8d
    8925:	48 83 c7 28          	add    $0x28,%rdi
    8929:	45 39 d0             	cmp    %r10d,%r8d
    892c:	0f 84 06 01 00 00    	je     8a38 <timer_thread+0x898>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    8932:	48 89 f8             	mov    %rdi,%rax
    8935:	48 c1 e8 03          	shr    $0x3,%rax
    8939:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    8940:	0f 85 10 05 00 00    	jne    8e56 <timer_thread+0xcb6>
    8946:	48 8b 07             	mov    (%rdi),%rax
    8949:	48 8d 50 08          	lea    0x8(%rax),%rdx
    894d:	48 89 d6             	mov    %rdx,%rsi
    8950:	48 c1 ee 03          	shr    $0x3,%rsi
    8954:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    895b:	0f 85 ed 04 00 00    	jne    8e4e <timer_thread+0xcae>
    8961:	4c 8b 48 08          	mov    0x8(%rax),%r9
    8965:	48 8d 47 08          	lea    0x8(%rdi),%rax
    8969:	48 89 c2             	mov    %rax,%rdx
    896c:	48 c1 ea 03          	shr    $0x3,%rdx
    8970:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    8977:	0f 85 c9 04 00 00    	jne    8e46 <timer_thread+0xca6>
    897d:	48 8b 47 08          	mov    0x8(%rdi),%rax
    8981:	48 8d 50 08          	lea    0x8(%rax),%rdx
    8985:	48 89 d6             	mov    %rdx,%rsi
    8988:	48 c1 ee 03          	shr    $0x3,%rsi
    898c:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    8993:	0f 85 a5 04 00 00    	jne    8e3e <timer_thread+0xc9e>
    8999:	48 8b 40 08          	mov    0x8(%rax),%rax
    899d:	4d 85 c9             	test   %r9,%r9
    89a0:	0f 8e 72 ff ff ff    	jle    8918 <timer_thread+0x778>
    89a6:	48 83 ec 08          	sub    $0x8,%rsp
    89aa:	89 ea                	mov    %ebp,%edx
    89ac:	bf 01 00 00 00       	mov    $0x1,%edi
    89b1:	50                   	push   %rax
    89b2:	48 8d 35 a7 87 00 00 	lea    0x87a7(%rip),%rsi        # 11160 <_IO_stdin_used+0x160>
    89b9:	31 c0                	xor    %eax,%eax
    89bb:	e8 60 bb ff ff       	call   4520 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    89c0:	4c 89 f0             	mov    %r14,%rax
    89c3:	5a                   	pop    %rdx
    89c4:	59                   	pop    %rcx
    89c5:	48 c1 e8 03          	shr    $0x3,%rax
    89c9:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    89d0:	84 c0                	test   %al,%al
    89d2:	74 08                	je     89dc <timer_thread+0x83c>
    89d4:	3c 03                	cmp    $0x3,%al
    89d6:	0f 8e 32 05 00 00    	jle    8f0e <timer_thread+0xd6e>
    89dc:	45 8b 57 30          	mov    0x30(%r15),%r10d
      for (int y = 0 ; y < 2 ; y++) {
    89e0:	48 83 fb 01          	cmp    $0x1,%rbx
    89e4:	74 6a                	je     8a50 <timer_thread+0x8b0>
    89e6:	48 83 c3 01          	add    $0x1,%rbx
    89ea:	c7 44 24 08 00 00 00 00 	movl   $0x0,0x8(%rsp)
    89f2:	89 d9                	mov    %ebx,%ecx
        for (int k = 0 ; k < data->my_thread_count; k++) {
    89f4:	45 85 d2             	test   %r10d,%r10d
    89f7:	0f 8f ab fe ff ff    	jg     88a8 <timer_thread+0x708>
    89fd:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    8a00:	49 83 c5 01          	add    $0x1,%r13
    8a04:	45 39 ea             	cmp    %r13d,%r10d
    8a07:	0f 8f 83 fe ff ff    	jg     8890 <timer_thread+0x6f0>
    if (all_empty == 1) {
    8a0d:	83 7c 24 08 01       	cmpl   $0x1,0x8(%rsp)
    8a12:	8b 6c 24 28          	mov    0x28(%rsp),%ebp
    8a16:	4c 8b 64 24 30       	mov    0x30(%rsp),%r12
    8a1b:	74 4a                	je     8a67 <timer_thread+0x8c7>
      nanosleep(&drain , &drainrem);
    8a1d:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    8a22:	49 8d 74 24 a0       	lea    -0x60(%r12),%rsi
    8a27:	e8 b4 bc ff ff       	call   46e0 <nanosleep@plt>
    8a2c:	e9 90 fc ff ff       	jmp    86c1 <timer_thread+0x521>
    8a31:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      for (int y = 0 ; y < 2 ; y++) {
    8a38:	48 8b 34 24          	mov    (%rsp),%rsi
    8a3c:	48 83 fb 01          	cmp    $0x1,%rbx
    8a40:	74 be                	je     8a00 <timer_thread+0x860>
    8a42:	48 83 c3 01          	add    $0x1,%rbx
    8a46:	89 d9                	mov    %ebx,%ecx
        for (int k = 0 ; k < data->my_thread_count; k++) {
    8a48:	e9 69 fe ff ff       	jmp    88b6 <timer_thread+0x716>
    8a4d:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    8a50:	49 83 c5 01          	add    $0x1,%r13
    8a54:	c7 44 24 08 00 00 00 00 	movl   $0x0,0x8(%rsp)
    8a5c:	45 39 ea             	cmp    %r13d,%r10d
    8a5f:	0f 8f 2b fe ff ff    	jg     8890 <timer_thread+0x6f0>
    8a65:	eb a6                	jmp    8a0d <timer_thread+0x86d>
    8a67:	48 8d 3d b2 86 00 00 	lea    0x86b2(%rip),%rdi        # 11120 <_IO_stdin_used+0x120>
    8a6e:	e8 8d bd ff ff       	call   4800 <puts@plt>
  while (data->running) {
    8a73:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    8a78:	48 89 d8             	mov    %rbx,%rax
    8a7b:	48 c1 e8 03          	shr    $0x3,%rax
    8a7f:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    8a86:	48 89 d8             	mov    %rbx,%rax
    8a89:	83 e0 07             	and    $0x7,%eax
    8a8c:	83 c0 03             	add    $0x3,%eax
    8a8f:	38 d0                	cmp    %dl,%al
    8a91:	7c 08                	jl     8a9b <timer_thread+0x8fb>
    8a93:	84 d2                	test   %dl,%dl
    8a95:	0f 85 fc 04 00 00    	jne    8f97 <timer_thread+0xdf7>
    8a9b:	41 8b 77 44          	mov    0x44(%r15),%esi
    8a9f:	85 f6                	test   %esi,%esi
    8aa1:	0f 84 12 03 00 00    	je     8db9 <timer_thread+0xc19>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    8aa7:	49 8d 5f 2c          	lea    0x2c(%r15),%rbx
    8aab:	48 89 d8             	mov    %rbx,%rax
    8aae:	48 c1 e8 03          	shr    $0x3,%rax
    8ab2:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    8ab9:	48 89 d8             	mov    %rbx,%rax
    8abc:	83 e0 07             	and    $0x7,%eax
    8abf:	83 c0 03             	add    $0x3,%eax
    8ac2:	38 d0                	cmp    %dl,%al
    8ac4:	7c 08                	jl     8ace <timer_thread+0x92e>
    8ac6:	84 d2                	test   %dl,%dl
    8ac8:	0f 85 c1 04 00 00    	jne    8f8f <timer_thread+0xdef>
    8ace:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    8ad2:	45 31 f6             	xor    %r14d,%r14d
    8ad5:	4c 8d 2d c4 86 00 00 	lea    0x86c4(%rip),%r13        # 111a0 <_IO_stdin_used+0x1a0>
    8adc:	85 c0                	test   %eax,%eax
    8ade:	0f 8e 84 01 00 00    	jle    8c68 <timer_thread+0xac8>
      data->threads[x]->running = 0;
    8ae4:	4c 8b 64 24 10       	mov    0x10(%rsp),%r12
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    8ae9:	48 89 dd             	mov    %rbx,%rbp
    8aec:	83 e5 07             	and    $0x7,%ebp
      data->threads[x]->running = 0;
    8aef:	49 c1 ec 03          	shr    $0x3,%r12
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    8af3:	83 c5 03             	add    $0x3,%ebp
    8af6:	eb 31                	jmp    8b29 <timer_thread+0x989>
    8af8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    8b00:	48 89 d8             	mov    %rbx,%rax
    8b03:	48 c1 e8 03          	shr    $0x3,%rax
    8b07:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    8b0e:	40 38 c5             	cmp    %al,%bpl
    8b11:	7c 08                	jl     8b1b <timer_thread+0x97b>
    8b13:	84 c0                	test   %al,%al
    8b15:	0f 85 c5 04 00 00    	jne    8fe0 <timer_thread+0xe40>
    8b1b:	49 83 c6 01          	add    $0x1,%r14
    8b1f:	45 39 77 2c          	cmp    %r14d,0x2c(%r15)
    8b23:	0f 8e 3f 01 00 00    	jle    8c68 <timer_thread+0xac8>
    8b29:	31 c0                	xor    %eax,%eax
    8b2b:	44 89 f2             	mov    %r14d,%edx
    8b2e:	4c 89 ee             	mov    %r13,%rsi
    8b31:	bf 01 00 00 00       	mov    $0x1,%edi
    8b36:	e8 e5 b9 ff ff       	call   4520 <__printf_chk@plt>
      data->threads[x]->running = 0;
    8b3b:	41 80 bc 24 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r12)
    8b44:	0f 85 3b 04 00 00    	jne    8f85 <timer_thread+0xde5>
    8b4a:	49 8b 7f 18          	mov    0x18(%r15),%rdi
    8b4e:	4a 8d 0c f5 00 00 00 00 	lea    0x0(,%r14,8),%rcx
    8b56:	48 01 cf             	add    %rcx,%rdi
    8b59:	48 89 f8             	mov    %rdi,%rax
    8b5c:	48 c1 e8 03          	shr    $0x3,%rax
    8b60:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    8b67:	0f 85 85 04 00 00    	jne    8ff2 <timer_thread+0xe52>
    8b6d:	48 8b 07             	mov    (%rdi),%rax
    8b70:	48 8d 78 44          	lea    0x44(%rax),%rdi
    8b74:	48 89 fa             	mov    %rdi,%rdx
    8b77:	48 c1 ea 03          	shr    $0x3,%rdx
    8b7b:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    8b82:	48 89 fa             	mov    %rdi,%rdx
    8b85:	83 e2 07             	and    $0x7,%edx
    8b88:	83 c2 03             	add    $0x3,%edx
    8b8b:	40 38 f2             	cmp    %sil,%dl
    8b8e:	7c 09                	jl     8b99 <timer_thread+0x9f9>
    8b90:	40 84 f6             	test   %sil,%sil
    8b93:	0f 85 54 04 00 00    	jne    8fed <timer_thread+0xe4d>
      if (data->threads[x]->type == IO) {
    8b99:	48 8d 78 0c          	lea    0xc(%rax),%rdi
      data->threads[x]->running = 0;
    8b9d:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    8ba4:	48 89 fa             	mov    %rdi,%rdx
    8ba7:	48 c1 ea 03          	shr    $0x3,%rdx
    8bab:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    8bb2:	48 89 fa             	mov    %rdi,%rdx
    8bb5:	83 e2 07             	and    $0x7,%edx
    8bb8:	83 c2 03             	add    $0x3,%edx
    8bbb:	40 38 f2             	cmp    %sil,%dl
    8bbe:	7c 09                	jl     8bc9 <timer_thread+0xa29>
    8bc0:	40 84 f6             	test   %sil,%sil
    8bc3:	0f 85 1f 04 00 00    	jne    8fe8 <timer_thread+0xe48>
    8bc9:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
    8bcd:	0f 85 2d ff ff ff    	jne    8b00 <timer_thread+0x960>
    8bd3:	48 8d 3d 06 86 00 00 	lea    0x8606(%rip),%rdi        # 111e0 <_IO_stdin_used+0x1e0>
    8bda:	48 89 0c 24          	mov    %rcx,(%rsp)
    8bde:	e8 1d bc ff ff       	call   4800 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    8be3:	48 8b 0c 24          	mov    (%rsp),%rcx
    8be7:	41 80 bc 24 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r12)
    8bf0:	0f 85 e0 03 00 00    	jne    8fd6 <timer_thread+0xe36>
    8bf6:	49 03 4f 18          	add    0x18(%r15),%rcx
    8bfa:	48 89 c8             	mov    %rcx,%rax
    8bfd:	48 c1 e8 03          	shr    $0x3,%rax
    8c01:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    8c08:	0f 85 c0 03 00 00    	jne    8fce <timer_thread+0xe2e>
    8c0e:	48 8b 01             	mov    (%rcx),%rax
    8c11:	48 8d 78 60          	lea    0x60(%rax),%rdi
    8c15:	48 89 fa             	mov    %rdi,%rdx
    8c18:	48 c1 ea 03          	shr    $0x3,%rdx
    8c1c:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    8c23:	84 d2                	test   %dl,%dl
    8c25:	74 09                	je     8c30 <timer_thread+0xa90>
    8c27:	80 fa 03             	cmp    $0x3,%dl
    8c2a:	0f 8e 99 03 00 00    	jle    8fc9 <timer_thread+0xe29>
    8c30:	8b 78 60             	mov    0x60(%rax),%edi
    8c33:	be 01 00 00 00       	mov    $0x1,%esi
    8c38:	e8 b3 bb ff ff       	call   47f0 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    8c3d:	48 89 d8             	mov    %rbx,%rax
    8c40:	48 c1 e8 03          	shr    $0x3,%rax
    8c44:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    8c4b:	40 38 c5             	cmp    %al,%bpl
    8c4e:	0f 8c c7 fe ff ff    	jl     8b1b <timer_thread+0x97b>
    8c54:	84 c0                	test   %al,%al
    8c56:	0f 84 bf fe ff ff    	je     8b1b <timer_thread+0x97b>
    8c5c:	48 89 df             	mov    %rbx,%rdi
    8c5f:	e8 ec b8 ff ff       	call   4550 <__asan_report_load4@plt>
    8c64:	0f 1f 40 00          	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    8c68:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    8c6d:	48 c1 e8 03          	shr    $0x3,%rax
    8c71:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    8c78:	84 c0                	test   %al,%al
    8c7a:	74 08                	je     8c84 <timer_thread+0xae4>
    8c7c:	3c 03                	cmp    $0x3,%al
    8c7e:	0f 8e 26 02 00 00    	jle    8eaa <timer_thread+0xd0a>
    8c84:	49 63 47 30          	movslq 0x30(%r15),%rax
    8c88:	85 c0                	test   %eax,%eax
    8c8a:	0f 8e ea 00 00 00    	jle    8d7a <timer_thread+0xbda>
      for (int y = 0 ; y < data->task_count ; y++) {
    8c90:	49 8d 7f 40          	lea    0x40(%r15),%rdi
    8c94:	48 89 fa             	mov    %rdi,%rdx
    8c97:	48 c1 ea 03          	shr    $0x3,%rdx
    8c9b:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    8ca2:	84 d2                	test   %dl,%dl
    8ca4:	74 09                	je     8caf <timer_thread+0xb0f>
    8ca6:	80 fa 03             	cmp    $0x3,%dl
    8ca9:	0f 8e cc 02 00 00    	jle    8f7b <timer_thread+0xddb>
    8caf:	4d 63 4f 40          	movslq 0x40(%r15),%r9
    8cb3:	4c 8d 04 c5 00 00 00 00 	lea    0x0(,%rax,8),%r8
    8cbb:	31 f6                	xor    %esi,%esi
    8cbd:	4c 89 ca             	mov    %r9,%rdx
    8cc0:	49 c1 e1 09          	shl    $0x9,%r9
    8cc4:	85 d2                	test   %edx,%edx
    8cc6:	0f 8e 4e 01 00 00    	jle    8e1a <timer_thread+0xc7a>
        data->threads[x]->tasks[y].scheduled = 0;
    8ccc:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    8cd1:	49 81 c1 4c 01 00 00 	add    $0x14c,%r9
    8cd8:	49 c1 ea 03          	shr    $0x3,%r10
    8cdc:	0f 1f 40 00          	nopl   0x0(%rax)
    8ce0:	41 80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r10)
    8ce8:	0f 85 83 02 00 00    	jne    8f71 <timer_thread+0xdd1>
    8cee:	49 8b 7f 18          	mov    0x18(%r15),%rdi
    8cf2:	48 01 f7             	add    %rsi,%rdi
    8cf5:	48 89 f8             	mov    %rdi,%rax
    8cf8:	48 c1 e8 03          	shr    $0x3,%rax
    8cfc:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    8d03:	0f 85 63 02 00 00    	jne    8f6c <timer_thread+0xdcc>
    8d09:	48 8b 07             	mov    (%rdi),%rax
    8d0c:	48 8d 78 38          	lea    0x38(%rax),%rdi
    8d10:	48 89 fa             	mov    %rdi,%rdx
    8d13:	48 c1 ea 03          	shr    $0x3,%rdx
    8d17:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    8d1e:	0f 85 04 02 00 00    	jne    8f28 <timer_thread+0xd88>
    8d24:	48 8b 48 38          	mov    0x38(%rax),%rcx
    8d28:	48 8d b9 4c 01 00 00 	lea    0x14c(%rcx),%rdi
    8d2f:	4c 01 c9             	add    %r9,%rcx
    8d32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    8d38:	48 89 f8             	mov    %rdi,%rax
    8d3b:	48 c1 e8 03          	shr    $0x3,%rax
    8d3f:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    8d46:	48 89 f8             	mov    %rdi,%rax
    8d49:	83 e0 07             	and    $0x7,%eax
    8d4c:	83 c0 03             	add    $0x3,%eax
    8d4f:	38 d0                	cmp    %dl,%al
    8d51:	7c 08                	jl     8d5b <timer_thread+0xbbb>
    8d53:	84 d2                	test   %dl,%dl
    8d55:	0f 85 00 01 00 00    	jne    8e5b <timer_thread+0xcbb>
    8d5b:	c7 07 00 00 00 00    	movl   $0x0,(%rdi)
      for (int y = 0 ; y < data->task_count ; y++) {
    8d61:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    8d68:	48 39 f9             	cmp    %rdi,%rcx
    8d6b:	75 cb                	jne    8d38 <timer_thread+0xb98>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    8d6d:	48 83 c6 08          	add    $0x8,%rsi
    8d71:	4c 39 c6             	cmp    %r8,%rsi
    8d74:	0f 85 66 ff ff ff    	jne    8ce0 <timer_thread+0xb40>
    asm volatile ("mfence" ::: "memory");
    8d7a:	0f ae f0             	mfence
    8d7d:	48 8d 3d 9c 84 00 00 	lea    0x849c(%rip),%rdi        # 11220 <_IO_stdin_used+0x220>
    8d84:	e8 77 ba ff ff       	call   4800 <puts@plt>
    data->running = 0;
    8d89:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    8d8e:	48 89 d8             	mov    %rbx,%rax
    8d91:	48 c1 e8 03          	shr    $0x3,%rax
    8d95:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    8d9c:	48 89 d8             	mov    %rbx,%rax
    8d9f:	83 e0 07             	and    $0x7,%eax
    8da2:	83 c0 03             	add    $0x3,%eax
    8da5:	38 d0                	cmp    %dl,%al
    8da7:	7c 08                	jl     8db1 <timer_thread+0xc11>
    8da9:	84 d2                	test   %dl,%dl
    8dab:	0f 85 b3 01 00 00    	jne    8f64 <timer_thread+0xdc4>
    8db1:	41 c7 47 44 00 00 00 00 	movl   $0x0,0x44(%r15)
    8db9:	48 8d 3d a0 84 00 00 	lea    0x84a0(%rip),%rdi        # 11260 <_IO_stdin_used+0x260>
    8dc0:	e8 3b ba ff ff       	call   4800 <puts@plt>
void* timer_thread(void *arg) {
    8dc5:	48 8b 5c 24 48       	mov    0x48(%rsp),%rbx
    8dca:	48 39 5c 24 60       	cmp    %rbx,0x60(%rsp)
    8dcf:	0f 85 58 01 00 00    	jne    8f2d <timer_thread+0xd8d>
    8dd5:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    8dda:	66 0f ef c0          	pxor   %xmm0,%xmm0
    8dde:	c7 80 10 80 ff 7f 00 00 00 00 	movl   $0x0,0x7fff8010(%rax)
    8de8:	0f 11 80 00 80 ff 7f 	movups %xmm0,0x7fff8000(%rax)
}
    8def:	48 8b 84 24 28 01 00 00 	mov    0x128(%rsp),%rax
    8df7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    8e00:	0f 85 f1 00 00 00    	jne    8ef7 <timer_thread+0xd57>
    8e06:	48 81 c4 38 01 00 00 	add    $0x138,%rsp
    8e0d:	31 c0                	xor    %eax,%eax
    8e0f:	5b                   	pop    %rbx
    8e10:	5d                   	pop    %rbp
    8e11:	41 5c                	pop    %r12
    8e13:	41 5d                	pop    %r13
    8e15:	41 5e                	pop    %r14
    8e17:	41 5f                	pop    %r15
    8e19:	c3                   	ret
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    8e1a:	48 83 c6 08          	add    $0x8,%rsi
    8e1e:	4c 39 c6             	cmp    %r8,%rsi
    8e21:	0f 85 9d fe ff ff    	jne    8cc4 <timer_thread+0xb24>
    8e27:	e9 4e ff ff ff       	jmp    8d7a <timer_thread+0xbda>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    8e2c:	48 83 c1 08          	add    $0x8,%rcx
    8e30:	48 39 f1             	cmp    %rsi,%rcx
    8e33:	0f 85 66 f7 ff ff    	jne    859f <timer_thread+0x3ff>
    8e39:	e9 0c f8 ff ff       	jmp    864a <timer_thread+0x4aa>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    8e3e:	48 89 d7             	mov    %rdx,%rdi
    8e41:	e8 9a b6 ff ff       	call   44e0 <__asan_report_load8@plt>
    8e46:	48 89 c7             	mov    %rax,%rdi
    8e49:	e8 92 b6 ff ff       	call   44e0 <__asan_report_load8@plt>
    8e4e:	48 89 d7             	mov    %rdx,%rdi
    8e51:	e8 8a b6 ff ff       	call   44e0 <__asan_report_load8@plt>
    8e56:	e8 85 b6 ff ff       	call   44e0 <__asan_report_load8@plt>
        data->threads[x]->tasks[y].scheduled = 0;
    8e5b:	e8 60 b8 ff ff       	call   46c0 <__asan_report_store4@plt>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    8e60:	e8 7b b6 ff ff       	call   44e0 <__asan_report_load8@plt>
    8e65:	48 89 f7             	mov    %rsi,%rdi
    8e68:	e8 73 b6 ff ff       	call   44e0 <__asan_report_load8@plt>
    8e6d:	e8 6e b6 ff ff       	call   44e0 <__asan_report_load8@plt>
        int next = (y + 1) % data->threads[x]->task_count;
    8e72:	e8 69 b6 ff ff       	call   44e0 <__asan_report_load8@plt>
    8e77:	48 89 d7             	mov    %rdx,%rdi
    8e7a:	e8 d1 b6 ff ff       	call   4550 <__asan_report_load4@plt>
        data->threads[x]->tasks[next].scheduled = 1;
    8e7f:	48 89 c7             	mov    %rax,%rdi
    8e82:	e8 59 b6 ff ff       	call   44e0 <__asan_report_load8@plt>
    8e87:	4c 89 c7             	mov    %r8,%rdi
    8e8a:	e8 31 b8 ff ff       	call   46c0 <__asan_report_store4@plt>
        data->threads[x]->tasks[y].scheduled = 0;
    8e8f:	48 89 d7             	mov    %rdx,%rdi
    8e92:	e8 29 b8 ff ff       	call   46c0 <__asan_report_store4@plt>
    8e97:	49 8d 47 30          	lea    0x30(%r15),%rax
    8e9b:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    8ea0:	e9 92 f6 ff ff       	jmp    8537 <timer_thread+0x397>
      data->threads[x]->tasks[y].sending = 0;
    8ea5:	e8 36 b6 ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    8eaa:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    8eaf:	e8 9c b6 ff ff       	call   4550 <__asan_report_load4@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    8eb4:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    8eb9:	e8 92 b6 ff ff       	call   4550 <__asan_report_load4@plt>
  while (data->running && n < times) {
    8ebe:	48 89 df             	mov    %rbx,%rdi
    8ec1:	e8 8a b6 ff ff       	call   4550 <__asan_report_load4@plt>
  struct timespec preempt = {
    8ec6:	e8 05 b8 ff ff       	call   46d0 <__asan_report_store8@plt>
    8ecb:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    8ed0:	e8 fb b7 ff ff       	call   46d0 <__asan_report_store8@plt>
  printf("In timer task %d\n", data->thread_index);
    8ed5:	e8 76 b6 ff ff       	call   4550 <__asan_report_load4@plt>
void* timer_thread(void *arg) {
    8eda:	bf a0 00 00 00       	mov    $0xa0,%edi
    8edf:	e8 ec b5 ff ff       	call   44d0 <__asan_stack_malloc_2@plt>
    8ee4:	48 85 c0             	test   %rax,%rax
    8ee7:	48 0f 44 44 24 48    	cmove  0x48(%rsp),%rax
    8eed:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    8ef2:	e9 e0 f2 ff ff       	jmp    81d7 <timer_thread+0x37>
}
    8ef7:	e8 b4 b7 ff ff       	call   46b0 <__stack_chk_fail@plt>
    8efc:	0f 1f 40 00          	nopl   0x0(%rax)
    if (y >= data->threads[0]->task_count) {
    8f00:	e8 db b5 ff ff       	call   44e0 <__asan_report_load8@plt>
    8f05:	48 8b 3c 24          	mov    (%rsp),%rdi
    8f09:	e8 d2 b5 ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    8f0e:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    8f13:	e8 38 b6 ff ff       	call   4550 <__asan_report_load4@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    8f18:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    8f1d:	e8 2e b6 ff ff       	call   4550 <__asan_report_load4@plt>
    8f22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        data->threads[x]->tasks[y].scheduled = 0;
    8f28:	e8 b3 b5 ff ff       	call   44e0 <__asan_report_load8@plt>
void* timer_thread(void *arg) {
    8f2d:	48 c7 03 0e 36 e0 45 	movq   $0x45e0360e,(%rbx)
    8f34:	48 89 d8             	mov    %rbx,%rax
    8f37:	66 0f 6f 05 91 a4 00 00 	movdqa 0xa491(%rip),%xmm0        # 133d0 <_IO_stdin_used+0x23d0>
    8f3f:	48 8b 5c 24 58       	mov    0x58(%rsp),%rbx
    8f44:	c7 83 10 80 ff 7f f5 f5 f5 f5 	movl   $0xf5f5f5f5,0x7fff8010(%rbx)
    8f4e:	0f 11 83 00 80 ff 7f 	movups %xmm0,0x7fff8000(%rbx)
    8f55:	48 8b 80 f8 00 00 00 	mov    0xf8(%rax),%rax
    8f5c:	c6 00 00             	movb   $0x0,(%rax)
    8f5f:	e9 8b fe ff ff       	jmp    8def <timer_thread+0xc4f>
    data->running = 0;
    8f64:	48 89 df             	mov    %rbx,%rdi
    8f67:	e8 54 b7 ff ff       	call   46c0 <__asan_report_store4@plt>
        data->threads[x]->tasks[y].scheduled = 0;
    8f6c:	e8 6f b5 ff ff       	call   44e0 <__asan_report_load8@plt>
    8f71:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    8f76:	e8 65 b5 ff ff       	call   44e0 <__asan_report_load8@plt>
      for (int y = 0 ; y < data->task_count ; y++) {
    8f7b:	e8 d0 b5 ff ff       	call   4550 <__asan_report_load4@plt>
    if (y >= data->threads[0]->task_count) {
    8f80:	e8 cb b5 ff ff       	call   4550 <__asan_report_load4@plt>
      data->threads[x]->running = 0;
    8f85:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    8f8a:	e8 51 b5 ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    8f8f:	48 89 df             	mov    %rbx,%rdi
    8f92:	e8 b9 b5 ff ff       	call   4550 <__asan_report_load4@plt>
  while (data->running) {
    8f97:	48 89 df             	mov    %rbx,%rdi
    8f9a:	e8 b1 b5 ff ff       	call   4550 <__asan_report_load4@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    8f9f:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    8fa4:	e8 a7 b5 ff ff       	call   4550 <__asan_report_load4@plt>
  while (data->running && n < times) {
    8fa9:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    8fae:	e8 9d b5 ff ff       	call   4550 <__asan_report_load4@plt>
      data->threads[x]->tasks[y].sending = 0;
    8fb3:	48 89 c7             	mov    %rax,%rdi
    8fb6:	e8 25 b5 ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int y = 0 ; y < data->task_count ; y++) {
    8fbb:	e8 90 b5 ff ff       	call   4550 <__asan_report_load4@plt>
        int next = (y + 1) % data->threads[x]->task_count;
    8fc0:	48 8b 3c 24          	mov    (%rsp),%rdi
    8fc4:	e8 17 b5 ff ff       	call   44e0 <__asan_report_load8@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    8fc9:	e8 82 b5 ff ff       	call   4550 <__asan_report_load4@plt>
    8fce:	48 89 cf             	mov    %rcx,%rdi
    8fd1:	e8 0a b5 ff ff       	call   44e0 <__asan_report_load8@plt>
    8fd6:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    8fdb:	e8 00 b5 ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    8fe0:	48 89 df             	mov    %rbx,%rdi
    8fe3:	e8 68 b5 ff ff       	call   4550 <__asan_report_load4@plt>
      if (data->threads[x]->type == IO) {
    8fe8:	e8 63 b5 ff ff       	call   4550 <__asan_report_load4@plt>
      data->threads[x]->running = 0;
    8fed:	e8 ce b6 ff ff       	call   46c0 <__asan_report_store4@plt>
    8ff2:	e8 e9 b4 ff ff       	call   44e0 <__asan_report_load8@plt>
    if (y >= data->threads[0]->task_count) {
    8ff7:	e8 54 b5 ff ff       	call   4550 <__asan_report_load4@plt>
    8ffc:	e8 df b4 ff ff       	call   44e0 <__asan_report_load8@plt>
    9001:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    9006:	e8 d5 b4 ff ff       	call   44e0 <__asan_report_load8@plt>
        data->threads[x]->tasks[y].scheduled = 0;
    900b:	48 89 d7             	mov    %rdx,%rdi
    900e:	e8 ad b6 ff ff       	call   46c0 <__asan_report_store4@plt>
        data->threads[x]->tasks[next].scheduled = 1;
    9013:	4c 89 c7             	mov    %r8,%rdi
    9016:	e8 a5 b6 ff ff       	call   46c0 <__asan_report_store4@plt>
    901b:	48 89 c7             	mov    %rax,%rdi
    901e:	e8 bd b4 ff ff       	call   44e0 <__asan_report_load8@plt>
        int next = (y + 1) % data->threads[x]->task_count;
    9023:	48 89 d7             	mov    %rdx,%rdi
    9026:	e8 25 b5 ff ff       	call   4550 <__asan_report_load4@plt>
    902b:	e8 b0 b4 ff ff       	call   44e0 <__asan_report_load8@plt>
    9030:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    9035:	e8 a6 b4 ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int x = 0 ; x < data->thread_count ; x++) {
    903a:	48 8b 7c 24 68       	mov    0x68(%rsp),%rdi
    903f:	e8 0c b5 ff ff       	call   4550 <__asan_report_load4@plt>
  struct timespec drain = {
    9044:	e8 87 b6 ff ff       	call   46d0 <__asan_report_store8@plt>
    9049:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    904e:	e8 7d b6 ff ff       	call   46d0 <__asan_report_store8@plt>
    9053:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->threads[x]->tasks[y].sending = 0;
    9058:	e8 63 b6 ff ff       	call   46c0 <__asan_report_store4@plt>
    905d:	e8 7e b4 ff ff       	call   44e0 <__asan_report_load8@plt>
    9062:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    906d:	0f 1f 00             	nopl   (%rax)

0000000000009070 <sendm.part.0>:
int sendm(struct BarrierTask *data) {
    9070:	41 57                	push   %r15
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    9072:	48 8d 97 40 01 00 00 	lea    0x140(%rdi),%rdx
int sendm(struct BarrierTask *data) {
    9079:	49 89 f8             	mov    %rdi,%r8
    907c:	41 56                	push   %r14
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    907e:	48 89 d0             	mov    %rdx,%rax
int sendm(struct BarrierTask *data) {
    9081:	41 55                	push   %r13
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    9083:	48 c1 e8 03          	shr    $0x3,%rax
int sendm(struct BarrierTask *data) {
    9087:	41 54                	push   %r12
    9089:	55                   	push   %rbp
    908a:	53                   	push   %rbx
    908b:	48 83 ec 68          	sub    $0x68,%rsp
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    908f:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    9096:	84 c0                	test   %al,%al
    9098:	74 08                	je     90a2 <sendm.part.0+0x32>
    909a:	3c 03                	cmp    $0x3,%al
    909c:	0f 8e 25 04 00 00    	jle    94c7 <sendm.part.0+0x457>
    90a2:	41 8b 80 40 01 00 00 	mov    0x140(%r8),%eax
    90a9:	45 31 ff             	xor    %r15d,%r15d
    90ac:	31 f6                	xor    %esi,%esi
    90ae:	49 8d 88 30 01 00 00 	lea    0x130(%r8),%rcx
    90b5:	85 c0                	test   %eax,%eax
    90b7:	0f 8e 9d 02 00 00    	jle    935a <sendm.part.0+0x2ea>
        if (n == data->thread_index) { continue; }
    90bd:	48 89 cf             	mov    %rcx,%rdi
    90c0:	48 89 54 24 38       	mov    %rdx,0x38(%rsp)
    90c5:	4d 89 fe             	mov    %r15,%r14
        struct Data *them = data->mailboxes[n].higher;
    90c8:	4d 8d 88 70 01 00 00 	lea    0x170(%r8),%r9
        if (n == data->thread_index) { continue; }
    90cf:	48 c1 ef 03          	shr    $0x3,%rdi
          data->n++;
    90d3:	49 8d 98 08 01 00 00 	lea    0x108(%r8),%rbx
    90da:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    90df:	4d 8d a0 88 01 00 00 	lea    0x188(%r8),%r12
        if (n == data->thread_index) { continue; }
    90e6:	48 89 3c 24          	mov    %rdi,(%rsp)
        struct Data *them = data->mailboxes[n].higher;
    90ea:	4c 89 cf             	mov    %r9,%rdi
          them->messages[them->messages_count++] = data->message; 
    90ed:	4d 89 e3             	mov    %r12,%r11
        struct Data *them = data->mailboxes[n].higher;
    90f0:	48 c1 ef 03          	shr    $0x3,%rdi
    90f4:	4c 89 4c 24 48       	mov    %r9,0x48(%rsp)
          them->messages[them->messages_count++] = data->message; 
    90f9:	49 c1 eb 03          	shr    $0x3,%r11
        struct Data *them = data->mailboxes[n].higher;
    90fd:	48 89 7c 24 20       	mov    %rdi,0x20(%rsp)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    9102:	48 89 d7             	mov    %rdx,%rdi
    9105:	48 c1 ef 03          	shr    $0x3,%rdi
    9109:	48 89 5c 24 50       	mov    %rbx,0x50(%rsp)
    910e:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
          data->n++;
    9113:	48 89 df             	mov    %rbx,%rdi
    9116:	48 c1 ef 03          	shr    $0x3,%rdi
    911a:	4c 89 64 24 58       	mov    %r12,0x58(%rsp)
    911f:	48 89 7c 24 30       	mov    %rdi,0x30(%rsp)
    9124:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread_index) { continue; }
    9128:	48 8b 0c 24          	mov    (%rsp),%rcx
    912c:	0f b6 91 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%edx
    9133:	84 d2                	test   %dl,%dl
    9135:	74 09                	je     9140 <sendm.part.0+0xd0>
    9137:	80 fa 03             	cmp    $0x3,%dl
    913a:	0f 8e 73 03 00 00    	jle    94b3 <sendm.part.0+0x443>
    9140:	41 39 b0 30 01 00 00 	cmp    %esi,0x130(%r8)
    9147:	0f 84 fe 01 00 00    	je     934b <sendm.part.0+0x2db>
        struct Data *them = data->mailboxes[n].higher;
    914d:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    9152:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    9159:	0f 85 4a 03 00 00    	jne    94a9 <sendm.part.0+0x439>
    915f:	49 8b 98 70 01 00 00 	mov    0x170(%r8),%rbx
    9166:	4c 01 f3             	add    %r14,%rbx
    9169:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    916d:	48 89 fa             	mov    %rdi,%rdx
    9170:	48 c1 ea 03          	shr    $0x3,%rdx
    9174:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    917b:	0f 85 23 03 00 00    	jne    94a4 <sendm.part.0+0x434>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    9181:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
        struct Data *them = data->mailboxes[n].higher;
    9185:	4c 8b 53 08          	mov    0x8(%rbx),%r10
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    9189:	48 89 fa             	mov    %rdi,%rdx
    918c:	48 c1 ea 03          	shr    $0x3,%rdx
    9190:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    9197:	84 d2                	test   %dl,%dl
    9199:	74 09                	je     91a4 <sendm.part.0+0x134>
    919b:	80 fa 03             	cmp    $0x3,%dl
    919e:	0f 8e fb 02 00 00    	jle    949f <sendm.part.0+0x42f>
    91a4:	44 8b 7b 20          	mov    0x20(%rbx),%r15d
    91a8:	41 83 ff 02          	cmp    $0x2,%r15d
    91ac:	0f 84 be 01 00 00    	je     9370 <sendm.part.0+0x300>
        int min = them->messages_limit;
    91b2:	49 8d 7a 10          	lea    0x10(%r10),%rdi
    91b6:	48 89 f8             	mov    %rdi,%rax
    91b9:	48 c1 e8 03          	shr    $0x3,%rax
    91bd:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    91c4:	0f 85 d0 02 00 00    	jne    949a <sendm.part.0+0x42a>
        for (; them->messages_count < min;) {
    91ca:	4d 8d 4a 08          	lea    0x8(%r10),%r9
        int min = them->messages_limit;
    91ce:	49 8b 42 10          	mov    0x10(%r10),%rax
        for (; them->messages_count < min;) {
    91d2:	4c 89 ca             	mov    %r9,%rdx
    91d5:	48 c1 ea 03          	shr    $0x3,%rdx
    91d9:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    91e0:	0f 85 ac 02 00 00    	jne    9492 <sendm.part.0+0x422>
    91e6:	49 8b 6a 08          	mov    0x8(%r10),%rbp
    91ea:	48 98                	cltq
    91ec:	48 39 c5             	cmp    %rax,%rbp
    91ef:	0f 8d 34 01 00 00    	jge    9329 <sendm.part.0+0x2b9>
          data->n++;
    91f5:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    91fa:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    9201:	0f 85 b6 02 00 00    	jne    94bd <sendm.part.0+0x44d>
          data->mailboxes[n].sent++;
    9207:	48 8d 7b 10          	lea    0x10(%rbx),%rdi
    920b:	49 8b 88 08 01 00 00 	mov    0x108(%r8),%rcx
    9212:	48 89 fa             	mov    %rdi,%rdx
    9215:	48 c1 ea 03          	shr    $0x3,%rdx
    9219:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    921e:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    9225:	0f 85 dd 02 00 00    	jne    9508 <sendm.part.0+0x498>
          them->messages[them->messages_count++] = data->message; 
    922b:	4c 89 d2             	mov    %r10,%rdx
    922e:	48 8b 4b 10          	mov    0x10(%rbx),%rcx
    9232:	48 c1 ea 03          	shr    $0x3,%rdx
    9236:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    923d:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    9242:	0f 85 b8 02 00 00    	jne    9500 <sendm.part.0+0x490>
    9248:	4d 8b 22             	mov    (%r10),%r12
        for (; them->messages_count < min;) {
    924b:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    9250:	4c 8d 2c ed 00 00 00 00 	lea    0x0(,%rbp,8),%r13
    9258:	48 89 ea             	mov    %rbp,%rdx
    925b:	4b 8d 3c 2c          	lea    (%r12,%r13,1),%rdi
    925f:	90                   	nop
          them->messages[them->messages_count++] = data->message; 
    9260:	48 83 c2 01          	add    $0x1,%rdx
    9264:	41 80 bb 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r11)
    926c:	0f 85 0c 02 00 00    	jne    947e <sendm.part.0+0x40e>
    9272:	48 89 fb             	mov    %rdi,%rbx
    9275:	49 8b 88 88 01 00 00 	mov    0x188(%r8),%rcx
    927c:	48 c1 eb 03          	shr    $0x3,%rbx
    9280:	80 bb 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rbx)
    9287:	0f 85 ec 01 00 00    	jne    9479 <sendm.part.0+0x409>
    928d:	48 89 0f             	mov    %rcx,(%rdi)
        for (; them->messages_count < min;) {
    9290:	48 83 c7 08          	add    $0x8,%rdi
    9294:	48 39 c2             	cmp    %rax,%rdx
    9297:	7c c7                	jl     9260 <sendm.part.0+0x1f0>
    9299:	48 39 c5             	cmp    %rax,%rbp
    929c:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    92a1:	0f 9c c2             	setl   %dl
    92a4:	48 83 e8 01          	sub    $0x1,%rax
    92a8:	31 ff                	xor    %edi,%edi
    92aa:	48 29 e8             	sub    %rbp,%rax
    92ad:	84 d2                	test   %dl,%dl
    92af:	48 0f 45 f8          	cmovne %rax,%rdi
    92b3:	48 c1 e0 03          	shl    $0x3,%rax
    92b7:	84 d2                	test   %dl,%dl
    92b9:	ba 00 00 00 00       	mov    $0x0,%edx
    92be:	48 0f 44 c2          	cmove  %rdx,%rax
    92c2:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    92c7:	48 8d 6c 3d 01       	lea    0x1(%rbp,%rdi,1),%rbp
    92cc:	48 8d 54 3a 01       	lea    0x1(%rdx,%rdi,1),%rdx
    92d1:	4c 01 e8             	add    %r13,%rax
    92d4:	49 89 90 08 01 00 00 	mov    %rdx,0x108(%r8)
    92db:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    92e0:	4c 01 e0             	add    %r12,%rax
    92e3:	48 8d 54 3a 01       	lea    0x1(%rdx,%rdi,1),%rdx
    92e8:	48 89 53 10          	mov    %rdx,0x10(%rbx)
          them->messages[them->messages_count++] = data->message; 
    92ec:	4c 89 ca             	mov    %r9,%rdx
    92ef:	48 c1 ea 03          	shr    $0x3,%rdx
    92f3:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    92fa:	0f 85 e8 01 00 00    	jne    94e8 <sendm.part.0+0x478>
    9300:	48 89 c2             	mov    %rax,%rdx
    9303:	49 89 6a 08          	mov    %rbp,0x8(%r10)
    9307:	48 c1 ea 03          	shr    $0x3,%rdx
    930b:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    9312:	0f 85 bc 01 00 00    	jne    94d4 <sendm.part.0+0x464>
    9318:	48 89 08             	mov    %rcx,(%rax)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    931b:	49 8d 7a 18          	lea    0x18(%r10),%rdi
    931f:	41 83 ff 02          	cmp    $0x2,%r15d
    9323:	0f 84 bf 00 00 00    	je     93e8 <sendm.part.0+0x378>
        asm volatile ("sfence" ::: "memory");
    9329:	0f ae f8             	sfence
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    932c:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    9331:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    9338:	84 c0                	test   %al,%al
    933a:	74 08                	je     9344 <sendm.part.0+0x2d4>
    933c:	3c 03                	cmp    $0x3,%al
    933e:	0f 8e 44 01 00 00    	jle    9488 <sendm.part.0+0x418>
    9344:	41 8b 80 40 01 00 00 	mov    0x140(%r8),%eax
    934b:	83 c6 01             	add    $0x1,%esi
    934e:	49 83 c6 28          	add    $0x28,%r14
    9352:	39 c6                	cmp    %eax,%esi
    9354:	0f 8c ce fd ff ff    	jl     9128 <sendm.part.0+0xb8>
}
    935a:	48 83 c4 68          	add    $0x68,%rsp
    935e:	5b                   	pop    %rbx
    935f:	5d                   	pop    %rbp
    9360:	41 5c                	pop    %r12
    9362:	41 5d                	pop    %r13
    9364:	41 5e                	pop    %r14
    9366:	41 5f                	pop    %r15
    9368:	c3                   	ret
    9369:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    9370:	49 8d 7a 18          	lea    0x18(%r10),%rdi
    9374:	48 89 fa             	mov    %rdi,%rdx
    9377:	48 c1 ea 03          	shr    $0x3,%rdx
    937b:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    9382:	84 d2                	test   %dl,%dl
    9384:	74 09                	je     938f <sendm.part.0+0x31f>
    9386:	80 fa 03             	cmp    $0x3,%dl
    9389:	0f 8e 40 01 00 00    	jle    94cf <sendm.part.0+0x45f>
    938f:	41 8b 52 18          	mov    0x18(%r10),%edx
    9393:	83 fa 01             	cmp    $0x1,%edx
    9396:	0f 84 98 00 00 00    	je     9434 <sendm.part.0+0x3c4>
        else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 0) {
    939c:	85 d2                	test   %edx,%edx
    939e:	74 ab                	je     934b <sendm.part.0+0x2db>
        int min = them->messages_limit;
    93a0:	49 8d 42 10          	lea    0x10(%r10),%rax
    93a4:	48 89 c2             	mov    %rax,%rdx
    93a7:	48 c1 ea 03          	shr    $0x3,%rdx
    93ab:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    93b2:	0f 85 3d 01 00 00    	jne    94f5 <sendm.part.0+0x485>
        for (; them->messages_count < min;) {
    93b8:	4d 8d 4a 08          	lea    0x8(%r10),%r9
        int min = them->messages_limit;
    93bc:	49 8b 52 10          	mov    0x10(%r10),%rdx
        for (; them->messages_count < min;) {
    93c0:	4c 89 c8             	mov    %r9,%rax
    93c3:	48 c1 e8 03          	shr    $0x3,%rax
    93c7:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    93ce:	0f 85 08 01 00 00    	jne    94dc <sendm.part.0+0x46c>
    93d4:	49 8b 6a 08          	mov    0x8(%r10),%rbp
    93d8:	48 63 c2             	movslq %edx,%rax
    93db:	48 39 c5             	cmp    %rax,%rbp
    93de:	0f 8c 11 fe ff ff    	jl     91f5 <sendm.part.0+0x185>
    93e4:	0f 1f 40 00          	nopl   0x0(%rax)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    93e8:	48 89 f8             	mov    %rdi,%rax
    93eb:	48 c1 e8 03          	shr    $0x3,%rax
    93ef:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    93f6:	84 c0                	test   %al,%al
    93f8:	74 08                	je     9402 <sendm.part.0+0x392>
    93fa:	3c 03                	cmp    $0x3,%al
    93fc:	0f 8e ee 00 00 00    	jle    94f0 <sendm.part.0+0x480>
    9402:	41 83 7a 18 01       	cmpl   $0x1,0x18(%r10)
    9407:	0f 85 1c ff ff ff    	jne    9329 <sendm.part.0+0x2b9>
          them->available = 0;
    940d:	48 89 f8             	mov    %rdi,%rax
    9410:	48 c1 e8 03          	shr    $0x3,%rax
    9414:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    941b:	84 c0                	test   %al,%al
    941d:	74 08                	je     9427 <sendm.part.0+0x3b7>
    941f:	3c 03                	cmp    $0x3,%al
    9421:	0f 8e e6 00 00 00    	jle    950d <sendm.part.0+0x49d>
    9427:	41 c7 42 18 00 00 00 00 	movl   $0x0,0x18(%r10)
    942f:	e9 f5 fe ff ff       	jmp    9329 <sendm.part.0+0x2b9>
        int min = them->messages_limit;
    9434:	49 8d 42 10          	lea    0x10(%r10),%rax
    9438:	48 89 c2             	mov    %rax,%rdx
    943b:	48 c1 ea 03          	shr    $0x3,%rdx
    943f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    9446:	0f 85 c6 00 00 00    	jne    9512 <sendm.part.0+0x4a2>
        for (; them->messages_count < min;) {
    944c:	4d 8d 4a 08          	lea    0x8(%r10),%r9
        int min = them->messages_limit;
    9450:	49 8b 42 10          	mov    0x10(%r10),%rax
        for (; them->messages_count < min;) {
    9454:	4c 89 ca             	mov    %r9,%rdx
    9457:	48 c1 ea 03          	shr    $0x3,%rdx
    945b:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    9462:	0f 85 b2 00 00 00    	jne    951a <sendm.part.0+0x4aa>
    9468:	49 8b 6a 08          	mov    0x8(%r10),%rbp
    946c:	48 98                	cltq
    946e:	48 39 e8             	cmp    %rbp,%rax
    9471:	0f 8f 7e fd ff ff    	jg     91f5 <sendm.part.0+0x185>
    9477:	eb 94                	jmp    940d <sendm.part.0+0x39d>
          them->messages[them->messages_count++] = data->message; 
    9479:	e8 52 b2 ff ff       	call   46d0 <__asan_report_store8@plt>
    947e:	48 8b 7c 24 58       	mov    0x58(%rsp),%rdi
    9483:	e8 58 b0 ff ff       	call   44e0 <__asan_report_load8@plt>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    9488:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    948d:	e8 be b0 ff ff       	call   4550 <__asan_report_load4@plt>
        for (; them->messages_count < min;) {
    9492:	4c 89 cf             	mov    %r9,%rdi
    9495:	e8 46 b0 ff ff       	call   44e0 <__asan_report_load8@plt>
        int min = them->messages_limit;
    949a:	e8 41 b0 ff ff       	call   44e0 <__asan_report_load8@plt>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    949f:	e8 ac b0 ff ff       	call   4550 <__asan_report_load4@plt>
        struct Data *them = data->mailboxes[n].higher;
    94a4:	e8 37 b0 ff ff       	call   44e0 <__asan_report_load8@plt>
    94a9:	48 8b 7c 24 48       	mov    0x48(%rsp),%rdi
    94ae:	e8 2d b0 ff ff       	call   44e0 <__asan_report_load8@plt>
        if (n == data->thread_index) { continue; }
    94b3:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    94b8:	e8 93 b0 ff ff       	call   4550 <__asan_report_load4@plt>
          data->n++;
    94bd:	48 8b 7c 24 50       	mov    0x50(%rsp),%rdi
    94c2:	e8 19 b0 ff ff       	call   44e0 <__asan_report_load8@plt>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    94c7:	48 89 d7             	mov    %rdx,%rdi
    94ca:	e8 81 b0 ff ff       	call   4550 <__asan_report_load4@plt>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    94cf:	e8 7c b0 ff ff       	call   4550 <__asan_report_load4@plt>
    94d4:	48 89 c7             	mov    %rax,%rdi
    94d7:	e8 f4 b1 ff ff       	call   46d0 <__asan_report_store8@plt>
        for (; them->messages_count < min;) {
    94dc:	4c 89 cf             	mov    %r9,%rdi
    94df:	e8 fc af ff ff       	call   44e0 <__asan_report_load8@plt>
    94e4:	0f 1f 40 00          	nopl   0x0(%rax)
          them->messages[them->messages_count++] = data->message; 
    94e8:	4c 89 cf             	mov    %r9,%rdi
    94eb:	e8 e0 b1 ff ff       	call   46d0 <__asan_report_store8@plt>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && them->available == 1) {
    94f0:	e8 5b b0 ff ff       	call   4550 <__asan_report_load4@plt>
        int min = them->messages_limit;
    94f5:	48 89 c7             	mov    %rax,%rdi
    94f8:	e8 e3 af ff ff       	call   44e0 <__asan_report_load8@plt>
    94fd:	0f 1f 00             	nopl   (%rax)
          them->messages[them->messages_count++] = data->message; 
    9500:	4c 89 d7             	mov    %r10,%rdi
    9503:	e8 d8 af ff ff       	call   44e0 <__asan_report_load8@plt>
          data->mailboxes[n].sent++;
    9508:	e8 d3 af ff ff       	call   44e0 <__asan_report_load8@plt>
          them->available = 0;
    950d:	e8 ae b1 ff ff       	call   46c0 <__asan_report_store4@plt>
        int min = them->messages_limit;
    9512:	48 89 c7             	mov    %rax,%rdi
    9515:	e8 c6 af ff ff       	call   44e0 <__asan_report_load8@plt>
        for (; them->messages_count < min;) {
    951a:	4c 89 cf             	mov    %r9,%rdi
    951d:	e8 be af ff ff       	call   44e0 <__asan_report_load8@plt>
    9522:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    952d:	0f 1f 00             	nopl   (%rax)

0000000000009530 <strtolower>:
void strtolower(char *str) {
    9530:	f3 0f 1e fa          	endbr64
    9534:	55                   	push   %rbp
    for (; *str; ++str)
    9535:	48 89 f8             	mov    %rdi,%rax
    9538:	48 89 fa             	mov    %rdi,%rdx
void strtolower(char *str) {
    953b:	53                   	push   %rbx
    for (; *str; ++str)
    953c:	48 c1 e8 03          	shr    $0x3,%rax
    9540:	83 e2 07             	and    $0x7,%edx
void strtolower(char *str) {
    9543:	48 89 fb             	mov    %rdi,%rbx
    9546:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    954a:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    9551:	38 d0                	cmp    %dl,%al
    9553:	7f 08                	jg     955d <strtolower+0x2d>
    9555:	84 c0                	test   %al,%al
    9557:	0f 85 a7 00 00 00    	jne    9604 <strtolower+0xd4>
    955d:	48 0f be 2b          	movsbq (%rbx),%rbp
    9561:	40 84 ed             	test   %bpl,%bpl
    9564:	0f 84 93 00 00 00    	je     95fd <strtolower+0xcd>
        *str = (char)tolower(*str);
    956a:	e8 81 b1 ff ff       	call   46f0 <__ctype_tolower_loc@plt>
    956f:	49 89 c0             	mov    %rax,%r8
    9572:	48 89 c6             	mov    %rax,%rsi
    9575:	49 c1 e8 03          	shr    $0x3,%r8
    9579:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    9580:	41 80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r8)
    9588:	0f 85 90 00 00 00    	jne    961e <strtolower+0xee>
    958e:	48 8b 06             	mov    (%rsi),%rax
    9591:	48 8d 3c a8          	lea    (%rax,%rbp,4),%rdi
    9595:	48 89 f8             	mov    %rdi,%rax
    9598:	48 c1 e8 03          	shr    $0x3,%rax
    959c:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    95a3:	48 89 f8             	mov    %rdi,%rax
    95a6:	83 e0 07             	and    $0x7,%eax
    95a9:	83 c0 03             	add    $0x3,%eax
    95ac:	38 d0                	cmp    %dl,%al
    95ae:	7c 04                	jl     95b4 <strtolower+0x84>
    95b0:	84 d2                	test   %dl,%dl
    95b2:	75 65                	jne    9619 <strtolower+0xe9>
    95b4:	48 89 d8             	mov    %rbx,%rax
    95b7:	48 89 d9             	mov    %rbx,%rcx
    95ba:	8b 17                	mov    (%rdi),%edx
    95bc:	48 c1 e8 03          	shr    $0x3,%rax
    95c0:	83 e1 07             	and    $0x7,%ecx
    95c3:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    95ca:	38 c8                	cmp    %cl,%al
    95cc:	7f 04                	jg     95d2 <strtolower+0xa2>
    95ce:	84 c0                	test   %al,%al
    95d0:	75 3f                	jne    9611 <strtolower+0xe1>
    95d2:	88 13                	mov    %dl,(%rbx)
    for (; *str; ++str)
    95d4:	48 83 c3 01          	add    $0x1,%rbx
    95d8:	48 89 d8             	mov    %rbx,%rax
    95db:	48 89 da             	mov    %rbx,%rdx
    95de:	48 c1 e8 03          	shr    $0x3,%rax
    95e2:	83 e2 07             	and    $0x7,%edx
    95e5:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    95ec:	38 d0                	cmp    %dl,%al
    95ee:	7f 04                	jg     95f4 <strtolower+0xc4>
    95f0:	84 c0                	test   %al,%al
    95f2:	75 15                	jne    9609 <strtolower+0xd9>
    95f4:	48 0f be 2b          	movsbq (%rbx),%rbp
    95f8:	40 84 ed             	test   %bpl,%bpl
    95fb:	75 83                	jne    9580 <strtolower+0x50>
}
    95fd:	48 83 c4 08          	add    $0x8,%rsp
    9601:	5b                   	pop    %rbx
    9602:	5d                   	pop    %rbp
    9603:	c3                   	ret
    for (; *str; ++str)
    9604:	e8 87 b1 ff ff       	call   4790 <__asan_report_load1@plt>
    9609:	48 89 df             	mov    %rbx,%rdi
    960c:	e8 7f b1 ff ff       	call   4790 <__asan_report_load1@plt>
        *str = (char)tolower(*str);
    9611:	48 89 df             	mov    %rbx,%rdi
    9614:	e8 b7 b1 ff ff       	call   47d0 <__asan_report_store1@plt>
    9619:	e8 32 af ff ff       	call   4550 <__asan_report_load4@plt>
    961e:	48 89 f7             	mov    %rsi,%rdi
    9621:	e8 ba ae ff ff       	call   44e0 <__asan_report_load8@plt>
    9626:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000009630 <zh_malloc>:
void *zh_malloc(size_t size) {
    9630:	f3 0f 1e fa          	endbr64
    9634:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    9638:	e8 53 af ff ff       	call   4590 <malloc@plt>
    if (!buf) {
    963d:	48 85 c0             	test   %rax,%rax
    9640:	74 05                	je     9647 <zh_malloc+0x17>
}
    9642:	48 83 c4 08          	add    $0x8,%rsp
    9646:	c3                   	ret
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    9647:	48 8d 3d d2 d4 00 00 	lea    0xd4d2(%rip),%rdi        # 16b20 <stderr@GLIBC_2.2.5>
    964e:	48 89 f8             	mov    %rdi,%rax
    9651:	48 c1 e8 03          	shr    $0x3,%rax
    9655:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    965c:	75 2c                	jne    968a <zh_malloc+0x5a>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    965e:	48 8b 0d bb d4 00 00 	mov    0xd4bb(%rip),%rcx        # 16b20 <stderr@GLIBC_2.2.5>
    9665:	ba 28 00 00 00       	mov    $0x28,%edx
    966a:	be 01 00 00 00       	mov    $0x1,%esi
    966f:	48 8d 3d 2a 7c 00 00 	lea    0x7c2a(%rip),%rdi        # 112a0 <_IO_stdin_used+0x2a0>
    9676:	e8 25 ae ff ff       	call   44a0 <fwrite@plt>
        exit(1);
    967b:	e8 90 af ff ff       	call   4610 <__asan_handle_no_return@plt>
    9680:	bf 01 00 00 00       	mov    $0x1,%edi
    9685:	e8 86 ae ff ff       	call   4510 <exit@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    968a:	e8 51 ae ff ff       	call   44e0 <__asan_report_load8@plt>
    968f:	90                   	nop

0000000000009690 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    9690:	f3 0f 1e fa          	endbr64
    9694:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    9695:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    969a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    969d:	e8 fe ae ff ff       	call   45a0 <strrchr@plt>
    if (!dot || dot == filename)
    96a2:	48 85 c0             	test   %rax,%rax
    96a5:	74 11                	je     96b8 <get_filename_ext+0x28>
    96a7:	48 39 c3             	cmp    %rax,%rbx
    96aa:	74 0c                	je     96b8 <get_filename_ext+0x28>
    return dot + 1;
    96ac:	48 83 c0 01          	add    $0x1,%rax
}
    96b0:	5b                   	pop    %rbx
    96b1:	c3                   	ret
    96b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    96b8:	48 8d 05 41 7c 00 00 	lea    0x7c41(%rip),%rax        # 11300 <_IO_stdin_used+0x300>
}
    96bf:	5b                   	pop    %rbx
    96c0:	c3                   	ret
    96c1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    96cc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000096d0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    96d0:	f3 0f 1e fa          	endbr64
    96d4:	41 57                	push   %r15
    96d6:	41 56                	push   %r14
    96d8:	41 55                	push   %r13
    96da:	41 54                	push   %r12
    96dc:	55                   	push   %rbp
    96dd:	48 89 fd             	mov    %rdi,%rbp
    96e0:	53                   	push   %rbx
    96e1:	48 89 d3             	mov    %rdx,%rbx
    96e4:	48 81 ec 58 09 00 00 	sub    $0x958,%rsp
    96eb:	8b 05 0f d4 00 00    	mov    0xd40f(%rip),%eax        # 16b00 <__asan_option_detect_stack_use_after_return@@Base>
    96f1:	4c 8d 74 24 10       	lea    0x10(%rsp),%r14
    96f6:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    96fb:	4c 89 34 24          	mov    %r14,(%rsp)
    96ff:	85 c0                	test   %eax,%eax
    9701:	0f 85 31 06 00 00    	jne    9d38 <send_headers+0x668>
    9707:	4d 89 f4             	mov    %r14,%r12
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    970a:	49 8d 7e 20          	lea    0x20(%r14),%rdi
    970e:	ba 00 04 00 00       	mov    $0x400,%edx
    9713:	48 89 ee             	mov    %rbp,%rsi
    9716:	48 8d 05 9b 97 00 00 	lea    0x979b(%rip),%rax        # 12eb8 <_IO_stdin_used+0x1eb8>
    971d:	49 c1 ec 03          	shr    $0x3,%r12
    9721:	49 c7 06 b3 8a b5 41 	movq   $0x41b58ab3,(%r14)
    9728:	4d 8d be 40 09 00 00 	lea    0x940(%r14),%r15
    972f:	49 89 46 08          	mov    %rax,0x8(%r14)
    9733:	48 8d 05 96 ff ff ff 	lea    -0x6a(%rip),%rax        # 96d0 <send_headers>
    973a:	49 89 46 10          	mov    %rax,0x10(%r14)
    973e:	41 c7 84 24 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%r12)
    974a:	41 c7 84 24 84 80 ff 7f f2 f2 f2 f2 	movl   $0xf2f2f2f2,0x7fff8084(%r12)
    9756:	41 c7 84 24 88 80 ff 7f f2 f2 f2 f2 	movl   $0xf2f2f2f2,0x7fff8088(%r12)
    9762:	41 c7 84 24 8c 80 ff 7f f2 f2 f2 f2 	movl   $0xf2f2f2f2,0x7fff808c(%r12)
    976e:	41 c7 84 24 90 80 ff 7f f2 f2 f2 f2 	movl   $0xf2f2f2f2,0x7fff8090(%r12)
    977a:	41 c7 84 24 14 81 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff8114(%r12)
    9786:	41 c7 84 24 18 81 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff8118(%r12)
    9792:	41 c7 84 24 1c 81 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff811c(%r12)
    979e:	41 c7 84 24 20 81 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff8120(%r12)
    97aa:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    97b3:	48 89 84 24 48 09 00 00 	mov    %rax,0x948(%rsp)
    97bb:	31 c0                	xor    %eax,%eax
    97bd:	e8 ae ae ff ff       	call   4670 <__strcpy_chk@plt>
    97c2:	48 89 c7             	mov    %rax,%rdi
    for (; *str; ++str)
    97c5:	48 c1 e8 03          	shr    $0x3,%rax
    97c9:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    97d0:	84 c0                	test   %al,%al
    97d2:	74 06                	je     97da <send_headers+0x10a>
    97d4:	0f 8e 47 05 00 00    	jle    9d21 <send_headers+0x651>
    97da:	49 0f be af e0 f6 ff ff 	movsbq -0x920(%r15),%rbp
    97e2:	40 84 ed             	test   %bpl,%bpl
    97e5:	0f 84 a0 00 00 00    	je     988b <send_headers+0x1bb>
        *str = (char)tolower(*str);
    97eb:	e8 00 af ff ff       	call   46f0 <__ctype_tolower_loc@plt>
    97f0:	48 89 c2             	mov    %rax,%rdx
    97f3:	48 c1 ea 03          	shr    $0x3,%rdx
    97f7:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    97fe:	0f 85 10 06 00 00    	jne    9e14 <send_headers+0x744>
    9804:	48 8b 08             	mov    (%rax),%rcx
    9807:	49 8d bf e0 f6 ff ff 	lea    -0x920(%r15),%rdi
    980e:	66 90                	xchg   %ax,%ax
    9810:	48 8d 04 a9          	lea    (%rcx,%rbp,4),%rax
    9814:	48 89 c2             	mov    %rax,%rdx
    9817:	48 c1 ea 03          	shr    $0x3,%rdx
    981b:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    9822:	48 89 c2             	mov    %rax,%rdx
    9825:	83 e2 07             	and    $0x7,%edx
    9828:	83 c2 03             	add    $0x3,%edx
    982b:	40 38 f2             	cmp    %sil,%dl
    982e:	7c 09                	jl     9839 <send_headers+0x169>
    9830:	40 84 f6             	test   %sil,%sil
    9833:	0f 85 ed 04 00 00    	jne    9d26 <send_headers+0x656>
    9839:	8b 10                	mov    (%rax),%edx
    983b:	48 89 f8             	mov    %rdi,%rax
    983e:	48 89 fe             	mov    %rdi,%rsi
    9841:	48 c1 e8 03          	shr    $0x3,%rax
    9845:	83 e6 07             	and    $0x7,%esi
    9848:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    984f:	40 38 f0             	cmp    %sil,%al
    9852:	7f 08                	jg     985c <send_headers+0x18c>
    9854:	84 c0                	test   %al,%al
    9856:	0f 85 d7 04 00 00    	jne    9d33 <send_headers+0x663>
    985c:	88 17                	mov    %dl,(%rdi)
    for (; *str; ++str)
    985e:	48 83 c7 01          	add    $0x1,%rdi
    9862:	48 89 f8             	mov    %rdi,%rax
    9865:	48 89 fa             	mov    %rdi,%rdx
    9868:	48 c1 e8 03          	shr    $0x3,%rax
    986c:	83 e2 07             	and    $0x7,%edx
    986f:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    9876:	38 d0                	cmp    %dl,%al
    9878:	7f 08                	jg     9882 <send_headers+0x1b2>
    987a:	84 c0                	test   %al,%al
    987c:	0f 85 ac 04 00 00    	jne    9d2e <send_headers+0x65e>
    9882:	48 0f be 2f          	movsbq (%rdi),%rbp
    9886:	40 84 ed             	test   %bpl,%bpl
    9889:	75 85                	jne    9810 <send_headers+0x140>
    void *buf = malloc(size);
    988b:	bf 11 00 00 00       	mov    $0x11,%edi
    9890:	e8 fb ac ff ff       	call   4590 <malloc@plt>
    9895:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    9898:	48 85 c0             	test   %rax,%rax
    989b:	0f 84 80 05 00 00    	je     9e21 <send_headers+0x751>
    iov[0].iov_base = zh_malloc(slen);
    98a1:	48 89 d8             	mov    %rbx,%rax
    98a4:	48 c1 e8 03          	shr    $0x3,%rax
    98a8:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    98af:	0f 85 e0 04 00 00    	jne    9d95 <send_headers+0x6c5>
    iov[0].iov_len = slen;
    98b5:	48 8d 43 08          	lea    0x8(%rbx),%rax
    iov[0].iov_base = zh_malloc(slen);
    98b9:	48 89 3b             	mov    %rdi,(%rbx)
    iov[0].iov_len = slen;
    98bc:	48 89 c2             	mov    %rax,%rdx
    98bf:	48 c1 ea 03          	shr    $0x3,%rdx
    98c3:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    98ca:	0f 85 dd 04 00 00    	jne    9dad <send_headers+0x6dd>
    98d0:	48 c7 43 08 11 00 00 00 	movq   $0x11,0x8(%rbx)
  return __builtin___memcpy_chk (__dest, __src, __len,
    98d8:	ba 11 00 00 00       	mov    $0x11,%edx
    98dd:	48 8d 35 5c 7a 00 00 	lea    0x7a5c(%rip),%rsi        # 11340 <_IO_stdin_used+0x340>
    98e4:	e8 d7 ab ff ff       	call   44c0 <memcpy@plt>
    void *buf = malloc(size);
    98e9:	bf 17 00 00 00       	mov    $0x17,%edi
    98ee:	e8 9d ac ff ff       	call   4590 <malloc@plt>
    98f3:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    98f6:	48 85 c0             	test   %rax,%rax
    98f9:	0f 84 f9 04 00 00    	je     9df8 <send_headers+0x728>
    iov[1].iov_base = zh_malloc(slen);
    98ff:	48 8d 43 10          	lea    0x10(%rbx),%rax
    9903:	48 89 c2             	mov    %rax,%rdx
    9906:	48 c1 ea 03          	shr    $0x3,%rdx
    990a:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    9911:	0f 85 8e 04 00 00    	jne    9da5 <send_headers+0x6d5>
    iov[1].iov_len = slen;
    9917:	48 8d 43 18          	lea    0x18(%rbx),%rax
    iov[1].iov_base = zh_malloc(slen);
    991b:	48 89 7b 10          	mov    %rdi,0x10(%rbx)
    iov[1].iov_len = slen;
    991f:	48 89 c2             	mov    %rax,%rdx
    9922:	48 c1 ea 03          	shr    $0x3,%rdx
    9926:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    992d:	0f 85 6a 04 00 00    	jne    9d9d <send_headers+0x6cd>
    9933:	48 c7 43 18 17 00 00 00 	movq   $0x17,0x18(%rbx)
    993b:	48 8d 35 3e 7a 00 00 	lea    0x7a3e(%rip),%rsi        # 11380 <_IO_stdin_used+0x380>
    9942:	ba 17 00 00 00       	mov    $0x17,%edx
    const char *dot = strrchr(filename, '.');
    9947:	49 8d af e0 f6 ff ff 	lea    -0x920(%r15),%rbp
    994e:	e8 6d ab ff ff       	call   44c0 <memcpy@plt>
    9953:	be 2e 00 00 00       	mov    $0x2e,%esi
    9958:	48 89 ef             	mov    %rbp,%rdi
    995b:	e8 40 ac ff ff       	call   45a0 <strrchr@plt>
    if (!dot || dot == filename)
    9960:	48 85 c0             	test   %rax,%rax
    9963:	0f 84 e7 02 00 00    	je     9c50 <send_headers+0x580>
    9969:	48 39 e8             	cmp    %rbp,%rax
    996c:	0f 84 de 02 00 00    	je     9c50 <send_headers+0x580>
    return dot + 1;
    9972:	48 8d 68 01          	lea    0x1(%rax),%rbp
    if (strcmp("jpg", file_ext) == 0)
    9976:	48 8d 3d 43 7a 00 00 	lea    0x7a43(%rip),%rdi        # 113c0 <_IO_stdin_used+0x3c0>
    997d:	48 89 ee             	mov    %rbp,%rsi
    9980:	e8 ab ad ff ff       	call   4730 <strcmp@plt>
    9985:	85 c0                	test   %eax,%eax
    9987:	0f 84 8b 02 00 00    	je     9c18 <send_headers+0x548>
    if (strcmp("jpeg", file_ext) == 0)
    998d:	48 89 ee             	mov    %rbp,%rsi
    9990:	48 8d 3d 69 7a 00 00 	lea    0x7a69(%rip),%rdi        # 11400 <_IO_stdin_used+0x400>
    9997:	4d 8d af 60 fb ff ff 	lea    -0x4a0(%r15),%r13
    999e:	e8 8d ad ff ff       	call   4730 <strcmp@plt>
    99a3:	85 c0                	test   %eax,%eax
    99a5:	75 14                	jne    99bb <send_headers+0x2eb>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    99a7:	ba 1b 00 00 00       	mov    $0x1b,%edx
    99ac:	48 8d 35 8d 7a 00 00 	lea    0x7a8d(%rip),%rsi        # 11440 <_IO_stdin_used+0x440>
    99b3:	4c 89 ef             	mov    %r13,%rdi
    99b6:	e8 05 ab ff ff       	call   44c0 <memcpy@plt>
    if (strcmp("png", file_ext) == 0)
    99bb:	48 89 ee             	mov    %rbp,%rsi
    99be:	48 8d 3d bb 7a 00 00 	lea    0x7abb(%rip),%rdi        # 11480 <_IO_stdin_used+0x480>
    99c5:	e8 66 ad ff ff       	call   4730 <strcmp@plt>
    99ca:	85 c0                	test   %eax,%eax
    99cc:	75 14                	jne    99e2 <send_headers+0x312>
    99ce:	ba 1a 00 00 00       	mov    $0x1a,%edx
    99d3:	48 8d 35 e6 7a 00 00 	lea    0x7ae6(%rip),%rsi        # 114c0 <_IO_stdin_used+0x4c0>
    99da:	4c 89 ef             	mov    %r13,%rdi
    99dd:	e8 de aa ff ff       	call   44c0 <memcpy@plt>
    if (strcmp("gif", file_ext) == 0)
    99e2:	48 89 ee             	mov    %rbp,%rsi
    99e5:	48 8d 3d 14 7b 00 00 	lea    0x7b14(%rip),%rdi        # 11500 <_IO_stdin_used+0x500>
    99ec:	e8 3f ad ff ff       	call   4730 <strcmp@plt>
    99f1:	85 c0                	test   %eax,%eax
    99f3:	0f 84 0f 03 00 00    	je     9d08 <send_headers+0x638>
    if (strcmp("htm", file_ext) == 0)
    99f9:	48 89 ee             	mov    %rbp,%rsi
    99fc:	48 8d 3d 7d 7b 00 00 	lea    0x7b7d(%rip),%rdi        # 11580 <_IO_stdin_used+0x580>
    9a03:	e8 28 ad ff ff       	call   4730 <strcmp@plt>
    9a08:	85 c0                	test   %eax,%eax
    9a0a:	0f 84 d8 02 00 00    	je     9ce8 <send_headers+0x618>
    if (strcmp("html", file_ext) == 0)
    9a10:	48 89 ee             	mov    %rbp,%rsi
    9a13:	48 8d 3d e6 7b 00 00 	lea    0x7be6(%rip),%rdi        # 11600 <_IO_stdin_used+0x600>
    9a1a:	e8 11 ad ff ff       	call   4730 <strcmp@plt>
    9a1f:	85 c0                	test   %eax,%eax
    9a21:	0f 84 a1 02 00 00    	je     9cc8 <send_headers+0x5f8>
    if (strcmp("js", file_ext) == 0)
    9a27:	48 89 ee             	mov    %rbp,%rsi
    9a2a:	48 8d 3d 0f 7c 00 00 	lea    0x7c0f(%rip),%rdi        # 11640 <_IO_stdin_used+0x640>
    9a31:	e8 fa ac ff ff       	call   4730 <strcmp@plt>
    9a36:	85 c0                	test   %eax,%eax
    9a38:	0f 84 6a 02 00 00    	je     9ca8 <send_headers+0x5d8>
    if (strcmp("css", file_ext) == 0)
    9a3e:	48 89 ee             	mov    %rbp,%rsi
    9a41:	48 8d 3d 98 7c 00 00 	lea    0x7c98(%rip),%rdi        # 116e0 <_IO_stdin_used+0x6e0>
    9a48:	e8 e3 ac ff ff       	call   4730 <strcmp@plt>
    9a4d:	85 c0                	test   %eax,%eax
    9a4f:	0f 84 33 02 00 00    	je     9c88 <send_headers+0x5b8>
    if (strcmp("txt", file_ext) == 0)
    9a55:	48 89 ee             	mov    %rbp,%rsi
    9a58:	48 8d 3d 01 7d 00 00 	lea    0x7d01(%rip),%rdi        # 11760 <_IO_stdin_used+0x760>
    9a5f:	e8 cc ac ff ff       	call   4730 <strcmp@plt>
    9a64:	85 c0                	test   %eax,%eax
    9a66:	0f 84 fc 01 00 00    	je     9c68 <send_headers+0x598>
    slen = strlen(send_buffer);
    9a6c:	4c 89 ef             	mov    %r13,%rdi
    9a6f:	e8 6c ab ff ff       	call   45e0 <strlen@plt>
    void *buf = malloc(size);
    9a74:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    9a77:	48 89 c5             	mov    %rax,%rbp
    void *buf = malloc(size);
    9a7a:	e8 11 ab ff ff       	call   4590 <malloc@plt>
    9a7f:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    9a82:	48 85 c0             	test   %rax,%rax
    9a85:	0f 84 b2 03 00 00    	je     9e3d <send_headers+0x76d>
    iov[2].iov_base = zh_malloc(slen);
    9a8b:	48 8d 43 20          	lea    0x20(%rbx),%rax
    9a8f:	48 89 c2             	mov    %rax,%rdx
    9a92:	48 c1 ea 03          	shr    $0x3,%rdx
    9a96:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    9a9d:	0f 85 da 02 00 00    	jne    9d7d <send_headers+0x6ad>
    iov[2].iov_len = slen;
    9aa3:	48 8d 43 28          	lea    0x28(%rbx),%rax
    iov[2].iov_base = zh_malloc(slen);
    9aa7:	48 89 7b 20          	mov    %rdi,0x20(%rbx)
    iov[2].iov_len = slen;
    9aab:	48 89 c2             	mov    %rax,%rdx
    9aae:	48 c1 ea 03          	shr    $0x3,%rdx
    9ab2:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    9ab9:	0f 85 c6 02 00 00    	jne    9d85 <send_headers+0x6b5>
    9abf:	48 89 6b 28          	mov    %rbp,0x28(%rbx)
  return __builtin___memcpy_chk (__dest, __src, __len,
    9ac3:	48 89 ea             	mov    %rbp,%rdx
    9ac6:	4c 89 ee             	mov    %r13,%rsi
    9ac9:	e8 f2 a9 ff ff       	call   44c0 <memcpy@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    9ace:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    9ad3:	4c 89 ef             	mov    %r13,%rdi
    9ad6:	31 c0                	xor    %eax,%eax
    9ad8:	48 8d 0d 01 7d 00 00 	lea    0x7d01(%rip),%rcx        # 117e0 <_IO_stdin_used+0x7e0>
    9adf:	ba 00 04 00 00       	mov    $0x400,%edx
    9ae4:	be 01 00 00 00       	mov    $0x1,%esi
    9ae9:	e8 32 ac ff ff       	call   4720 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    9aee:	4c 89 ef             	mov    %r13,%rdi
    9af1:	e8 ea aa ff ff       	call   45e0 <strlen@plt>
    void *buf = malloc(size);
    9af6:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    9af9:	48 89 c5             	mov    %rax,%rbp
    void *buf = malloc(size);
    9afc:	e8 8f aa ff ff       	call   4590 <malloc@plt>
    9b01:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    9b04:	48 85 c0             	test   %rax,%rax
    9b07:	0f 84 a8 02 00 00    	je     9db5 <send_headers+0x6e5>
    iov[3].iov_base = zh_malloc(slen);
    9b0d:	48 8d 43 30          	lea    0x30(%rbx),%rax
    9b11:	48 89 c2             	mov    %rax,%rdx
    9b14:	48 c1 ea 03          	shr    $0x3,%rdx
    9b18:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    9b1f:	0f 85 68 02 00 00    	jne    9d8d <send_headers+0x6bd>
    iov[3].iov_len = slen;
    9b25:	48 8d 43 38          	lea    0x38(%rbx),%rax
    iov[3].iov_base = zh_malloc(slen);
    9b29:	48 89 7b 30          	mov    %rdi,0x30(%rbx)
    iov[3].iov_len = slen;
    9b2d:	48 89 c2             	mov    %rax,%rdx
    9b30:	48 c1 ea 03          	shr    $0x3,%rdx
    9b34:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    9b3b:	0f 85 0d 02 00 00    	jne    9d4e <send_headers+0x67e>
    9b41:	48 89 6b 38          	mov    %rbp,0x38(%rbx)
    9b45:	48 89 ea             	mov    %rbp,%rdx
    9b48:	4c 89 ee             	mov    %r13,%rsi
    9b4b:	e8 70 a9 ff ff       	call   44c0 <memcpy@plt>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    9b50:	4c 89 ef             	mov    %r13,%rdi
    9b53:	ba 03 00 00 00       	mov    $0x3,%edx
    9b58:	48 8d 35 c1 7c 00 00 	lea    0x7cc1(%rip),%rsi        # 11820 <_IO_stdin_used+0x820>
    9b5f:	e8 5c a9 ff ff       	call   44c0 <memcpy@plt>
    void *buf = malloc(size);
    9b64:	bf 02 00 00 00       	mov    $0x2,%edi
    9b69:	e8 22 aa ff ff       	call   4590 <malloc@plt>
    if (!buf) {
    9b6e:	48 85 c0             	test   %rax,%rax
    9b71:	0f 84 e6 02 00 00    	je     9e5d <send_headers+0x78d>
    iov[4].iov_base = zh_malloc(slen);
    9b77:	48 8d 7b 40          	lea    0x40(%rbx),%rdi
    9b7b:	48 89 fa             	mov    %rdi,%rdx
    9b7e:	48 c1 ea 03          	shr    $0x3,%rdx
    9b82:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    9b89:	0f 85 c7 01 00 00    	jne    9d56 <send_headers+0x686>
    iov[4].iov_len = slen;
    9b8f:	48 8d 7b 48          	lea    0x48(%rbx),%rdi
    iov[4].iov_base = zh_malloc(slen);
    9b93:	48 89 43 40          	mov    %rax,0x40(%rbx)
    iov[4].iov_len = slen;
    9b97:	48 89 fa             	mov    %rdi,%rdx
    9b9a:	48 c1 ea 03          	shr    $0x3,%rdx
    9b9e:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    9ba5:	0f 85 b0 01 00 00    	jne    9d5b <send_headers+0x68b>
  return __builtin___memcpy_chk (__dest, __src, __len,
    9bab:	41 0f b7 97 60 fb ff ff 	movzwl -0x4a0(%r15),%edx
    9bb3:	48 c7 43 48 02 00 00 00 	movq   $0x2,0x48(%rbx)
    9bbb:	66 89 10             	mov    %dx,(%rax)
void send_headers(const char *path, off_t len, struct iovec *iov) {
    9bbe:	4c 39 34 24          	cmp    %r14,(%rsp)
    9bc2:	0f 85 98 01 00 00    	jne    9d60 <send_headers+0x690>
    9bc8:	41 c7 84 24 00 80 ff 7f 00 00 00 00 	movl   $0x0,0x7fff8000(%r12)
    9bd4:	66 0f ef c0          	pxor   %xmm0,%xmm0
    9bd8:	41 0f 11 84 24 84 80 ff 7f 	movups %xmm0,0x7fff8084(%r12)
    9be1:	41 0f 11 84 24 14 81 ff 7f 	movups %xmm0,0x7fff8114(%r12)
}
    9bea:	48 8b 84 24 48 09 00 00 	mov    0x948(%rsp),%rax
    9bf2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    9bfb:	0f 85 7c 02 00 00    	jne    9e7d <send_headers+0x7ad>
    9c01:	48 81 c4 58 09 00 00 	add    $0x958,%rsp
    9c08:	5b                   	pop    %rbx
    9c09:	5d                   	pop    %rbp
    9c0a:	41 5c                	pop    %r12
    9c0c:	41 5d                	pop    %r13
    9c0e:	41 5e                	pop    %r14
    9c10:	41 5f                	pop    %r15
    9c12:	c3                   	ret
    9c13:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    9c18:	4d 8d af 60 fb ff ff 	lea    -0x4a0(%r15),%r13
    9c1f:	ba 1b 00 00 00       	mov    $0x1b,%edx
    9c24:	48 8d 35 15 78 00 00 	lea    0x7815(%rip),%rsi        # 11440 <_IO_stdin_used+0x440>
    9c2b:	4c 89 ef             	mov    %r13,%rdi
    9c2e:	e8 8d a8 ff ff       	call   44c0 <memcpy@plt>
    if (strcmp("jpeg", file_ext) == 0)
    9c33:	48 89 ee             	mov    %rbp,%rsi
    9c36:	48 8d 3d c3 77 00 00 	lea    0x77c3(%rip),%rdi        # 11400 <_IO_stdin_used+0x400>
    9c3d:	e8 ee aa ff ff       	call   4730 <strcmp@plt>
    9c42:	e9 5c fd ff ff       	jmp    99a3 <send_headers+0x2d3>
    9c47:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        return "";
    9c50:	48 8d 2d a9 76 00 00 	lea    0x76a9(%rip),%rbp        # 11300 <_IO_stdin_used+0x300>
    9c57:	4d 8d af 60 fb ff ff 	lea    -0x4a0(%r15),%r13
    9c5e:	e9 7f fd ff ff       	jmp    99e2 <send_headers+0x312>
    9c63:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    9c68:	ba 1b 00 00 00       	mov    $0x1b,%edx
    9c6d:	48 8d 35 2c 7b 00 00 	lea    0x7b2c(%rip),%rsi        # 117a0 <_IO_stdin_used+0x7a0>
    9c74:	4c 89 ef             	mov    %r13,%rdi
    9c77:	e8 44 a8 ff ff       	call   44c0 <memcpy@plt>
    9c7c:	e9 eb fd ff ff       	jmp    9a6c <send_headers+0x39c>
    9c81:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    9c88:	ba 19 00 00 00       	mov    $0x19,%edx
    9c8d:	48 8d 35 8c 7a 00 00 	lea    0x7a8c(%rip),%rsi        # 11720 <_IO_stdin_used+0x720>
    9c94:	4c 89 ef             	mov    %r13,%rdi
    9c97:	e8 24 a8 ff ff       	call   44c0 <memcpy@plt>
    9c9c:	e9 b4 fd ff ff       	jmp    9a55 <send_headers+0x385>
    9ca1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    9ca8:	ba 27 00 00 00       	mov    $0x27,%edx
    9cad:	48 8d 35 cc 79 00 00 	lea    0x79cc(%rip),%rsi        # 11680 <_IO_stdin_used+0x680>
    9cb4:	4c 89 ef             	mov    %r13,%rdi
    9cb7:	e8 04 a8 ff ff       	call   44c0 <memcpy@plt>
    9cbc:	e9 7d fd ff ff       	jmp    9a3e <send_headers+0x36e>
    9cc1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    9cc8:	ba 1a 00 00 00       	mov    $0x1a,%edx
    9ccd:	48 8d 35 ec 78 00 00 	lea    0x78ec(%rip),%rsi        # 115c0 <_IO_stdin_used+0x5c0>
    9cd4:	4c 89 ef             	mov    %r13,%rdi
    9cd7:	e8 e4 a7 ff ff       	call   44c0 <memcpy@plt>
    9cdc:	e9 46 fd ff ff       	jmp    9a27 <send_headers+0x357>
    9ce1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    9ce8:	ba 1a 00 00 00       	mov    $0x1a,%edx
    9ced:	48 8d 35 cc 78 00 00 	lea    0x78cc(%rip),%rsi        # 115c0 <_IO_stdin_used+0x5c0>
    9cf4:	4c 89 ef             	mov    %r13,%rdi
    9cf7:	e8 c4 a7 ff ff       	call   44c0 <memcpy@plt>
    9cfc:	e9 0f fd ff ff       	jmp    9a10 <send_headers+0x340>
    9d01:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    9d08:	ba 1a 00 00 00       	mov    $0x1a,%edx
    9d0d:	48 8d 35 2c 78 00 00 	lea    0x782c(%rip),%rsi        # 11540 <_IO_stdin_used+0x540>
    9d14:	4c 89 ef             	mov    %r13,%rdi
    9d17:	e8 a4 a7 ff ff       	call   44c0 <memcpy@plt>
    9d1c:	e9 d8 fc ff ff       	jmp    99f9 <send_headers+0x329>
    for (; *str; ++str)
    9d21:	e8 6a aa ff ff       	call   4790 <__asan_report_load1@plt>
        *str = (char)tolower(*str);
    9d26:	48 89 c7             	mov    %rax,%rdi
    9d29:	e8 22 a8 ff ff       	call   4550 <__asan_report_load4@plt>
    for (; *str; ++str)
    9d2e:	e8 5d aa ff ff       	call   4790 <__asan_report_load1@plt>
        *str = (char)tolower(*str);
    9d33:	e8 98 aa ff ff       	call   47d0 <__asan_report_store1@plt>
void send_headers(const char *path, off_t len, struct iovec *iov) {
    9d38:	bf 20 09 00 00       	mov    $0x920,%edi
    9d3d:	e8 fe a7 ff ff       	call   4540 <__asan_stack_malloc_6@plt>
    9d42:	48 85 c0             	test   %rax,%rax
    9d45:	4c 0f 45 f0          	cmovne %rax,%r14
    9d49:	e9 b9 f9 ff ff       	jmp    9707 <send_headers+0x37>
    iov[3].iov_len = slen;
    9d4e:	48 89 c7             	mov    %rax,%rdi
    9d51:	e8 7a a9 ff ff       	call   46d0 <__asan_report_store8@plt>
    iov[4].iov_base = zh_malloc(slen);
    9d56:	e8 75 a9 ff ff       	call   46d0 <__asan_report_store8@plt>
    iov[4].iov_len = slen;
    9d5b:	e8 70 a9 ff ff       	call   46d0 <__asan_report_store8@plt>
void send_headers(const char *path, off_t len, struct iovec *iov) {
    9d60:	49 c7 06 0e 36 e0 45 	movq   $0x45e0360e,(%r14)
    9d67:	48 8b 14 24          	mov    (%rsp),%rdx
    9d6b:	be 20 09 00 00       	mov    $0x920,%esi
    9d70:	4c 89 f7             	mov    %r14,%rdi
    9d73:	e8 98 a9 ff ff       	call   4710 <__asan_stack_free_6@plt>
    9d78:	e9 6d fe ff ff       	jmp    9bea <send_headers+0x51a>
    iov[2].iov_base = zh_malloc(slen);
    9d7d:	48 89 c7             	mov    %rax,%rdi
    9d80:	e8 4b a9 ff ff       	call   46d0 <__asan_report_store8@plt>
    iov[2].iov_len = slen;
    9d85:	48 89 c7             	mov    %rax,%rdi
    9d88:	e8 43 a9 ff ff       	call   46d0 <__asan_report_store8@plt>
    iov[3].iov_base = zh_malloc(slen);
    9d8d:	48 89 c7             	mov    %rax,%rdi
    9d90:	e8 3b a9 ff ff       	call   46d0 <__asan_report_store8@plt>
    iov[0].iov_base = zh_malloc(slen);
    9d95:	48 89 df             	mov    %rbx,%rdi
    9d98:	e8 33 a9 ff ff       	call   46d0 <__asan_report_store8@plt>
    iov[1].iov_len = slen;
    9d9d:	48 89 c7             	mov    %rax,%rdi
    9da0:	e8 2b a9 ff ff       	call   46d0 <__asan_report_store8@plt>
    iov[1].iov_base = zh_malloc(slen);
    9da5:	48 89 c7             	mov    %rax,%rdi
    9da8:	e8 23 a9 ff ff       	call   46d0 <__asan_report_store8@plt>
    iov[0].iov_len = slen;
    9dad:	48 89 c7             	mov    %rax,%rdi
    9db0:	e8 1b a9 ff ff       	call   46d0 <__asan_report_store8@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    9db5:	48 8d 3d 64 cd 00 00 	lea    0xcd64(%rip),%rdi        # 16b20 <stderr@GLIBC_2.2.5>
    9dbc:	48 89 f8             	mov    %rdi,%rax
    9dbf:	48 c1 e8 03          	shr    $0x3,%rax
    9dc3:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    9dca:	75 50                	jne    9e1c <send_headers+0x74c>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    9dcc:	48 8b 0d 4d cd 00 00 	mov    0xcd4d(%rip),%rcx        # 16b20 <stderr@GLIBC_2.2.5>
    9dd3:	ba 28 00 00 00       	mov    $0x28,%edx
    9dd8:	be 01 00 00 00       	mov    $0x1,%esi
    9ddd:	48 8d 3d bc 74 00 00 	lea    0x74bc(%rip),%rdi        # 112a0 <_IO_stdin_used+0x2a0>
    9de4:	e8 b7 a6 ff ff       	call   44a0 <fwrite@plt>
        exit(1);
    9de9:	e8 22 a8 ff ff       	call   4610 <__asan_handle_no_return@plt>
    9dee:	bf 01 00 00 00       	mov    $0x1,%edi
    9df3:	e8 18 a7 ff ff       	call   4510 <exit@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    9df8:	48 8d 3d 21 cd 00 00 	lea    0xcd21(%rip),%rdi        # 16b20 <stderr@GLIBC_2.2.5>
    9dff:	48 89 f8             	mov    %rdi,%rax
    9e02:	48 c1 e8 03          	shr    $0x3,%rax
    9e06:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    9e0d:	74 bd                	je     9dcc <send_headers+0x6fc>
    9e0f:	e8 cc a6 ff ff       	call   44e0 <__asan_report_load8@plt>
        *str = (char)tolower(*str);
    9e14:	48 89 c7             	mov    %rax,%rdi
    9e17:	e8 c4 a6 ff ff       	call   44e0 <__asan_report_load8@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    9e1c:	e8 bf a6 ff ff       	call   44e0 <__asan_report_load8@plt>
    9e21:	48 8d 3d f8 cc 00 00 	lea    0xccf8(%rip),%rdi        # 16b20 <stderr@GLIBC_2.2.5>
    9e28:	48 89 f8             	mov    %rdi,%rax
    9e2b:	48 c1 e8 03          	shr    $0x3,%rax
    9e2f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    9e36:	74 94                	je     9dcc <send_headers+0x6fc>
    9e38:	e8 a3 a6 ff ff       	call   44e0 <__asan_report_load8@plt>
    9e3d:	48 8d 3d dc cc 00 00 	lea    0xccdc(%rip),%rdi        # 16b20 <stderr@GLIBC_2.2.5>
    9e44:	48 89 f8             	mov    %rdi,%rax
    9e47:	48 c1 e8 03          	shr    $0x3,%rax
    9e4b:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    9e52:	0f 84 74 ff ff ff    	je     9dcc <send_headers+0x6fc>
    9e58:	e8 83 a6 ff ff       	call   44e0 <__asan_report_load8@plt>
    9e5d:	48 8d 3d bc cc 00 00 	lea    0xccbc(%rip),%rdi        # 16b20 <stderr@GLIBC_2.2.5>
    9e64:	48 89 f8             	mov    %rdi,%rax
    9e67:	48 c1 e8 03          	shr    $0x3,%rax
    9e6b:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    9e72:	0f 84 54 ff ff ff    	je     9dcc <send_headers+0x6fc>
    9e78:	e8 63 a6 ff ff       	call   44e0 <__asan_report_load8@plt>
}
    9e7d:	e8 2e a8 ff ff       	call   46b0 <__stack_chk_fail@plt>
    9e82:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    9e8d:	0f 1f 00             	nopl   (%rax)

0000000000009e90 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    9e90:	f3 0f 1e fa          	endbr64
    9e94:	41 55                	push   %r13
    9e96:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    9e99:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    9e9c:	41 54                	push   %r12
    9e9e:	55                   	push   %rbp
    9e9f:	48 89 f5             	mov    %rsi,%rbp
    9ea2:	53                   	push   %rbx
    9ea3:	48 89 d3             	mov    %rdx,%rbx
    9ea6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    9eaa:	e8 e1 a6 ff ff       	call   4590 <malloc@plt>
    if (!buf) {
    9eaf:	48 85 c0             	test   %rax,%rax
    9eb2:	0f 84 b3 00 00 00    	je     9f6b <copy_file_contents+0xdb>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    9eb8:	4c 89 ef             	mov    %r13,%rdi
    9ebb:	49 89 c4             	mov    %rax,%r12
    9ebe:	31 f6                	xor    %esi,%esi
    9ec0:	31 c0                	xor    %eax,%eax
    9ec2:	e8 59 a9 ff ff       	call   4820 <open@plt>
    9ec7:	41 89 c5             	mov    %eax,%r13d
    if (fd < 0)
    9eca:	85 c0                	test   %eax,%eax
    9ecc:	0f 88 89 a9 ff ff    	js     485b <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    9ed2:	48 89 ea             	mov    %rbp,%rdx
    9ed5:	4c 89 e6             	mov    %r12,%rsi
    9ed8:	89 c7                	mov    %eax,%edi
    9eda:	e8 21 a7 ff ff       	call   4600 <read@plt>
    if (ret < file_size) {
    9edf:	48 98                	cltq
    9ee1:	48 39 e8             	cmp    %rbp,%rax
    9ee4:	7c 42                	jl     9f28 <copy_file_contents+0x98>
    close(fd);
    9ee6:	44 89 ef             	mov    %r13d,%edi
    9ee9:	e8 a2 a5 ff ff       	call   4490 <close@plt>
    iov->iov_base = buf;
    9eee:	48 89 d8             	mov    %rbx,%rax
    9ef1:	48 c1 e8 03          	shr    $0x3,%rax
    9ef5:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    9efc:	75 65                	jne    9f63 <copy_file_contents+0xd3>
    iov->iov_len = file_size;
    9efe:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    iov->iov_base = buf;
    9f02:	4c 89 23             	mov    %r12,(%rbx)
    iov->iov_len = file_size;
    9f05:	48 89 f8             	mov    %rdi,%rax
    9f08:	48 c1 e8 03          	shr    $0x3,%rax
    9f0c:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    9f13:	75 49                	jne    9f5e <copy_file_contents+0xce>
    9f15:	48 89 6b 08          	mov    %rbp,0x8(%rbx)
}
    9f19:	48 83 c4 08          	add    $0x8,%rsp
    9f1d:	5b                   	pop    %rbx
    9f1e:	5d                   	pop    %rbp
    9f1f:	41 5c                	pop    %r12
    9f21:	41 5d                	pop    %r13
    9f23:	c3                   	ret
    9f24:	0f 1f 40 00          	nopl   0x0(%rax)
        fprintf(stderr, "Encountered a short read.\n");
    9f28:	48 8d 3d f1 cb 00 00 	lea    0xcbf1(%rip),%rdi        # 16b20 <stderr@GLIBC_2.2.5>
    9f2f:	48 89 f8             	mov    %rdi,%rax
    9f32:	48 c1 e8 03          	shr    $0x3,%rax
    9f36:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    9f3d:	75 6f                	jne    9fae <copy_file_contents+0x11e>
    9f3f:	48 8b 0d da cb 00 00 	mov    0xcbda(%rip),%rcx        # 16b20 <stderr@GLIBC_2.2.5>
    9f46:	ba 1a 00 00 00       	mov    $0x1a,%edx
    9f4b:	be 01 00 00 00       	mov    $0x1,%esi
    9f50:	48 8d 3d 49 79 00 00 	lea    0x7949(%rip),%rdi        # 118a0 <_IO_stdin_used+0x8a0>
    9f57:	e8 44 a5 ff ff       	call   44a0 <fwrite@plt>
    9f5c:	eb 88                	jmp    9ee6 <copy_file_contents+0x56>
    iov->iov_len = file_size;
    9f5e:	e8 6d a7 ff ff       	call   46d0 <__asan_report_store8@plt>
    iov->iov_base = buf;
    9f63:	48 89 df             	mov    %rbx,%rdi
    9f66:	e8 65 a7 ff ff       	call   46d0 <__asan_report_store8@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    9f6b:	48 8d 3d ae cb 00 00 	lea    0xcbae(%rip),%rdi        # 16b20 <stderr@GLIBC_2.2.5>
    9f72:	48 89 f8             	mov    %rdi,%rax
    9f75:	48 c1 e8 03          	shr    $0x3,%rax
    9f79:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    9f80:	75 31                	jne    9fb3 <copy_file_contents+0x123>
    9f82:	48 8b 0d 97 cb 00 00 	mov    0xcb97(%rip),%rcx        # 16b20 <stderr@GLIBC_2.2.5>
    9f89:	ba 28 00 00 00       	mov    $0x28,%edx
    9f8e:	be 01 00 00 00       	mov    $0x1,%esi
    9f93:	48 8d 3d 06 73 00 00 	lea    0x7306(%rip),%rdi        # 112a0 <_IO_stdin_used+0x2a0>
    9f9a:	e8 01 a5 ff ff       	call   44a0 <fwrite@plt>
        exit(1);
    9f9f:	e8 6c a6 ff ff       	call   4610 <__asan_handle_no_return@plt>
    9fa4:	bf 01 00 00 00       	mov    $0x1,%edi
    9fa9:	e8 62 a5 ff ff       	call   4510 <exit@plt>
        fprintf(stderr, "Encountered a short read.\n");
    9fae:	e8 2d a5 ff ff       	call   44e0 <__asan_report_load8@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    9fb3:	e8 28 a5 ff ff       	call   44e0 <__asan_report_load8@plt>
    9fb8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000009fc0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    9fc0:	f3 0f 1e fa          	endbr64
    9fc4:	48 89 fa             	mov    %rdi,%rdx
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    9fc7:	48 8d 7e 44          	lea    0x44(%rsi),%rdi
    9fcb:	48 83 ec 08          	sub    $0x8,%rsp
    9fcf:	48 89 f0             	mov    %rsi,%rax
    9fd2:	48 89 f9             	mov    %rdi,%rcx
    9fd5:	48 c1 e9 03          	shr    $0x3,%rcx
    9fd9:	0f b6 b1 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%esi
    9fe0:	48 89 f9             	mov    %rdi,%rcx
    9fe3:	83 e1 07             	and    $0x7,%ecx
    9fe6:	83 c1 03             	add    $0x3,%ecx
    9fe9:	40 38 f1             	cmp    %sil,%cl
    9fec:	7c 09                	jl     9ff7 <add_write_request+0x37>
    9fee:	40 84 f6             	test   %sil,%sil
    9ff1:	0f 85 ee 03 00 00    	jne    a3e5 <add_write_request+0x425>
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    9ff7:	48 8d b8 c0 00 00 00 	lea    0xc0(%rax),%rdi
	unsigned int head, next = sq->sqe_tail + 1;
    9ffe:	8b 70 44             	mov    0x44(%rax),%esi
	if (ring->flags & IORING_SETUP_SQE128)
    a001:	48 89 f9             	mov    %rdi,%rcx
    a004:	48 c1 e9 03          	shr    $0x3,%rcx
	unsigned int head, next = sq->sqe_tail + 1;
    a008:	83 c6 01             	add    $0x1,%esi
	if (ring->flags & IORING_SETUP_SQE128)
    a00b:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    a012:	84 c9                	test   %cl,%cl
    a014:	74 09                	je     a01f <add_write_request+0x5f>
    a016:	80 f9 03             	cmp    $0x3,%cl
    a019:	0f 8e c1 03 00 00    	jle    a3e0 <add_write_request+0x420>
    a01f:	8b 88 c0 00 00 00    	mov    0xc0(%rax),%ecx
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    a025:	48 89 c7             	mov    %rax,%rdi
    a028:	48 c1 ef 03          	shr    $0x3,%rdi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    a02c:	41 89 c8             	mov    %ecx,%r8d
    a02f:	41 83 e0 02          	and    $0x2,%r8d
		head = IO_URING_READ_ONCE(*sq->khead);
    a033:	80 bf 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdi)
    a03a:	0f 85 19 04 00 00    	jne    a459 <add_write_request+0x499>
    a040:	48 8b 38             	mov    (%rax),%rdi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    a043:	45 85 c0             	test   %r8d,%r8d
		head = IO_URING_READ_ONCE(*sq->khead);
    a046:	49 89 f8             	mov    %rdi,%r8
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    a049:	0f 85 61 03 00 00    	jne    a3b0 <add_write_request+0x3f0>
		head = IO_URING_READ_ONCE(*sq->khead);
    a04f:	49 c1 e8 03          	shr    $0x3,%r8
    a053:	45 0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%r8),%r9d
    a05b:	49 89 f8             	mov    %rdi,%r8
    a05e:	41 83 e0 07          	and    $0x7,%r8d
    a062:	41 83 c0 03          	add    $0x3,%r8d
    a066:	45 38 c8             	cmp    %r9b,%r8b
    a069:	7c 09                	jl     a074 <add_write_request+0xb4>
    a06b:	45 84 c9             	test   %r9b,%r9b
    a06e:	0f 85 e0 03 00 00    	jne    a454 <add_write_request+0x494>
    a074:	8b 3f                	mov    (%rdi),%edi
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    a076:	4c 8d 40 5c          	lea    0x5c(%rax),%r8
    a07a:	41 89 f2             	mov    %esi,%r10d
    a07d:	41 29 fa             	sub    %edi,%r10d
    a080:	4c 89 c7             	mov    %r8,%rdi
    a083:	48 c1 ef 03          	shr    $0x3,%rdi
    a087:	44 0f b6 8f 00 80 ff 7f 	movzbl 0x7fff8000(%rdi),%r9d
    a08f:	4c 89 c7             	mov    %r8,%rdi
    a092:	83 e7 07             	and    $0x7,%edi
    a095:	83 c7 03             	add    $0x3,%edi
    a098:	44 38 cf             	cmp    %r9b,%dil
    a09b:	7c 09                	jl     a0a6 <add_write_request+0xe6>
    a09d:	45 84 c9             	test   %r9b,%r9b
    a0a0:	0f 85 32 03 00 00    	jne    a3d8 <add_write_request+0x418>
    a0a6:	44 39 50 5c          	cmp    %r10d,0x5c(%rax)
    a0aa:	0f 82 bc a7 ff ff    	jb     486c <add_write_request.cold>
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    a0b0:	48 8d 78 38          	lea    0x38(%rax),%rdi
    a0b4:	49 89 f8             	mov    %rdi,%r8
    a0b7:	49 c1 e8 03          	shr    $0x3,%r8
    a0bb:	41 80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r8)
    a0c3:	0f 85 a0 03 00 00    	jne    a469 <add_write_request+0x4a9>
    a0c9:	4c 8d 50 58          	lea    0x58(%rax),%r10
    a0cd:	48 8b 78 38          	mov    0x38(%rax),%rdi
    a0d1:	44 8b 40 44          	mov    0x44(%rax),%r8d
    a0d5:	4d 89 d1             	mov    %r10,%r9
    a0d8:	49 c1 e9 03          	shr    $0x3,%r9
    a0dc:	45 0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%r9),%r9d
    a0e4:	45 84 c9             	test   %r9b,%r9b
    a0e7:	74 0a                	je     a0f3 <add_write_request+0x133>
    a0e9:	41 80 f9 03          	cmp    $0x3,%r9b
    a0ed:	0f 8e ff 02 00 00    	jle    a3f2 <add_write_request+0x432>
	if (ring->flags & IORING_SETUP_SQE128)
    a0f3:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    a0f6:	44 23 40 58          	and    0x58(%rax),%r8d
		sq->sqe_tail = next;
    a0fa:	89 70 44             	mov    %esi,0x44(%rax)
	if (ring->flags & IORING_SETUP_SQE128)
    a0fd:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    a100:	41 d3 e0             	shl    %cl,%r8d
    req->event_type = EVENT_TYPE_WRITE;
    a103:	48 89 d1             	mov    %rdx,%rcx
    a106:	48 c1 e9 03          	shr    $0x3,%rcx
    a10a:	49 c1 e0 06          	shl    $0x6,%r8
    a10e:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    a115:	4c 01 c7             	add    %r8,%rdi
    a118:	84 c9                	test   %cl,%cl
    a11a:	74 09                	je     a125 <add_write_request+0x165>
    a11c:	80 f9 03             	cmp    $0x3,%cl
    a11f:	0f 8e c5 02 00 00    	jle    a3ea <add_write_request+0x42a>
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    a125:	48 8d 72 04          	lea    0x4(%rdx),%rsi
    req->event_type = EVENT_TYPE_WRITE;
    a129:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    a12f:	48 89 f1             	mov    %rsi,%rcx
    a132:	48 c1 e9 03          	shr    $0x3,%rcx
    a136:	44 0f b6 81 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%r8d
    a13e:	48 89 f1             	mov    %rsi,%rcx
    a141:	83 e1 07             	and    $0x7,%ecx
    a144:	83 c1 03             	add    $0x3,%ecx
    a147:	44 38 c1             	cmp    %r8b,%cl
    a14a:	7c 09                	jl     a155 <add_write_request+0x195>
    a14c:	45 84 c0             	test   %r8b,%r8b
    a14f:	0f 85 ba 02 00 00    	jne    a40f <add_write_request+0x44f>
    a155:	48 8d 72 08          	lea    0x8(%rdx),%rsi
    a159:	44 8b 4a 04          	mov    0x4(%rdx),%r9d
    a15d:	4c 8d 52 10          	lea    0x10(%rdx),%r10
    a161:	48 89 f1             	mov    %rsi,%rcx
    a164:	48 c1 e9 03          	shr    $0x3,%rcx
    a168:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    a16f:	84 c9                	test   %cl,%cl
    a171:	74 09                	je     a17c <add_write_request+0x1bc>
    a173:	80 f9 03             	cmp    $0x3,%cl
    a176:	0f 8e 8b 02 00 00    	jle    a407 <add_write_request+0x447>
	sqe->opcode = (__u8) op;
    a17c:	48 89 f9             	mov    %rdi,%rcx
    a17f:	44 8b 5a 08          	mov    0x8(%rdx),%r11d
    a183:	48 c1 e9 03          	shr    $0x3,%rcx
    a187:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    a18e:	84 c9                	test   %cl,%cl
    a190:	74 06                	je     a198 <add_write_request+0x1d8>
    a192:	0f 8e 6a 02 00 00    	jle    a402 <add_write_request+0x442>
	sqe->flags = 0;
    a198:	48 8d 4f 01          	lea    0x1(%rdi),%rcx
	sqe->opcode = (__u8) op;
    a19c:	c6 07 02             	movb   $0x2,(%rdi)
	sqe->flags = 0;
    a19f:	48 89 ce             	mov    %rcx,%rsi
    a1a2:	49 89 c8             	mov    %rcx,%r8
    a1a5:	48 c1 ee 03          	shr    $0x3,%rsi
    a1a9:	41 83 e0 07          	and    $0x7,%r8d
    a1ad:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    a1b4:	44 38 c6             	cmp    %r8b,%sil
    a1b7:	7f 09                	jg     a1c2 <add_write_request+0x202>
    a1b9:	40 84 f6             	test   %sil,%sil
    a1bc:	0f 85 38 02 00 00    	jne    a3fa <add_write_request+0x43a>
	sqe->ioprio = 0;
    a1c2:	48 8d 77 02          	lea    0x2(%rdi),%rsi
	sqe->flags = 0;
    a1c6:	c6 47 01 00          	movb   $0x0,0x1(%rdi)
	sqe->ioprio = 0;
    a1ca:	48 89 f1             	mov    %rsi,%rcx
    a1cd:	48 c1 e9 03          	shr    $0x3,%rcx
    a1d1:	44 0f b6 81 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%r8d
    a1d9:	48 89 f1             	mov    %rsi,%rcx
    a1dc:	83 e1 07             	and    $0x7,%ecx
    a1df:	83 c1 01             	add    $0x1,%ecx
    a1e2:	44 38 c1             	cmp    %r8b,%cl
    a1e5:	7c 09                	jl     a1f0 <add_write_request+0x230>
    a1e7:	45 84 c0             	test   %r8b,%r8b
    a1ea:	0f 85 57 02 00 00    	jne    a447 <add_write_request+0x487>
	sqe->fd = fd;
    a1f0:	48 8d 77 04          	lea    0x4(%rdi),%rsi
	sqe->ioprio = 0;
    a1f4:	45 31 c0             	xor    %r8d,%r8d
	sqe->fd = fd;
    a1f7:	48 89 f1             	mov    %rsi,%rcx
	sqe->ioprio = 0;
    a1fa:	66 44 89 47 02       	mov    %r8w,0x2(%rdi)
	sqe->fd = fd;
    a1ff:	48 c1 e9 03          	shr    $0x3,%rcx
    a203:	44 0f b6 81 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%r8d
    a20b:	48 89 f1             	mov    %rsi,%rcx
    a20e:	83 e1 07             	and    $0x7,%ecx
    a211:	83 c1 03             	add    $0x3,%ecx
    a214:	44 38 c1             	cmp    %r8b,%cl
    a217:	7c 09                	jl     a222 <add_write_request+0x262>
    a219:	45 84 c0             	test   %r8b,%r8b
    a21c:	0f 85 1d 02 00 00    	jne    a43f <add_write_request+0x47f>
	sqe->off = offset;
    a222:	48 8d 4f 08          	lea    0x8(%rdi),%rcx
	sqe->fd = fd;
    a226:	44 89 5f 04          	mov    %r11d,0x4(%rdi)
	sqe->off = offset;
    a22a:	48 89 ce             	mov    %rcx,%rsi
    a22d:	48 c1 ee 03          	shr    $0x3,%rsi
    a231:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    a238:	0f 85 23 02 00 00    	jne    a461 <add_write_request+0x4a1>
	sqe->addr = (unsigned long) addr;
    a23e:	48 8d 4f 10          	lea    0x10(%rdi),%rcx
	sqe->off = offset;
    a242:	48 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%rdi)
	sqe->addr = (unsigned long) addr;
    a24a:	48 89 ce             	mov    %rcx,%rsi
    a24d:	48 c1 ee 03          	shr    $0x3,%rsi
    a251:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    a258:	0f 85 28 02 00 00    	jne    a486 <add_write_request+0x4c6>
	sqe->len = len;
    a25e:	48 8d 77 18          	lea    0x18(%rdi),%rsi
	sqe->addr = (unsigned long) addr;
    a262:	4c 89 57 10          	mov    %r10,0x10(%rdi)
	sqe->len = len;
    a266:	48 89 f1             	mov    %rsi,%rcx
    a269:	48 c1 e9 03          	shr    $0x3,%rcx
    a26d:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    a274:	84 c9                	test   %cl,%cl
    a276:	74 09                	je     a281 <add_write_request+0x2c1>
    a278:	80 f9 03             	cmp    $0x3,%cl
    a27b:	0f 8e b6 01 00 00    	jle    a437 <add_write_request+0x477>
	sqe->rw_flags = 0;
    a281:	48 8d 77 1c          	lea    0x1c(%rdi),%rsi
	sqe->len = len;
    a285:	44 89 4f 18          	mov    %r9d,0x18(%rdi)
	sqe->rw_flags = 0;
    a289:	48 89 f1             	mov    %rsi,%rcx
    a28c:	48 c1 e9 03          	shr    $0x3,%rcx
    a290:	44 0f b6 81 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%r8d
    a298:	48 89 f1             	mov    %rsi,%rcx
    a29b:	83 e1 07             	and    $0x7,%ecx
    a29e:	83 c1 03             	add    $0x3,%ecx
    a2a1:	44 38 c1             	cmp    %r8b,%cl
    a2a4:	7c 09                	jl     a2af <add_write_request+0x2ef>
    a2a6:	45 84 c0             	test   %r8b,%r8b
    a2a9:	0f 85 80 01 00 00    	jne    a42f <add_write_request+0x46f>
	sqe->buf_index = 0;
    a2af:	48 8d 77 28          	lea    0x28(%rdi),%rsi
	sqe->rw_flags = 0;
    a2b3:	c7 47 1c 00 00 00 00 	movl   $0x0,0x1c(%rdi)
	sqe->buf_index = 0;
    a2ba:	48 89 f1             	mov    %rsi,%rcx
    a2bd:	48 c1 e9 03          	shr    $0x3,%rcx
    a2c1:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    a2c8:	84 c9                	test   %cl,%cl
    a2ca:	74 09                	je     a2d5 <add_write_request+0x315>
    a2cc:	80 f9 01             	cmp    $0x1,%cl
    a2cf:	0f 8e 52 01 00 00    	jle    a427 <add_write_request+0x467>
    a2d5:	31 f6                	xor    %esi,%esi
    a2d7:	66 89 77 28          	mov    %si,0x28(%rdi)
	sqe->personality = 0;
    a2db:	48 8d 77 2a          	lea    0x2a(%rdi),%rsi
    a2df:	48 89 f1             	mov    %rsi,%rcx
    a2e2:	48 c1 e9 03          	shr    $0x3,%rcx
    a2e6:	44 0f b6 81 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%r8d
    a2ee:	48 89 f1             	mov    %rsi,%rcx
    a2f1:	83 e1 07             	and    $0x7,%ecx
    a2f4:	83 c1 01             	add    $0x1,%ecx
    a2f7:	44 38 c1             	cmp    %r8b,%cl
    a2fa:	7c 09                	jl     a305 <add_write_request+0x345>
    a2fc:	45 84 c0             	test   %r8b,%r8b
    a2ff:	0f 85 1a 01 00 00    	jne    a41f <add_write_request+0x45f>
    a305:	31 c9                	xor    %ecx,%ecx
	sqe->file_index = 0;
    a307:	48 8d 77 2c          	lea    0x2c(%rdi),%rsi
	sqe->personality = 0;
    a30b:	66 89 4f 2a          	mov    %cx,0x2a(%rdi)
	sqe->file_index = 0;
    a30f:	48 89 f1             	mov    %rsi,%rcx
    a312:	48 c1 e9 03          	shr    $0x3,%rcx
    a316:	44 0f b6 81 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%r8d
    a31e:	48 89 f1             	mov    %rsi,%rcx
    a321:	83 e1 07             	and    $0x7,%ecx
    a324:	83 c1 03             	add    $0x3,%ecx
    a327:	44 38 c1             	cmp    %r8b,%cl
    a32a:	7c 09                	jl     a335 <add_write_request+0x375>
    a32c:	45 84 c0             	test   %r8b,%r8b
    a32f:	0f 85 e2 00 00 00    	jne    a417 <add_write_request+0x457>
	sqe->addr3 = 0;
    a335:	48 8d 4f 30          	lea    0x30(%rdi),%rcx
	sqe->file_index = 0;
    a339:	c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%rdi)
	sqe->addr3 = 0;
    a340:	48 89 ce             	mov    %rcx,%rsi
    a343:	48 c1 ee 03          	shr    $0x3,%rsi
    a347:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    a34e:	0f 85 22 01 00 00    	jne    a476 <add_write_request+0x4b6>
	sqe->__pad2[0] = 0;
    a354:	48 8d 4f 38          	lea    0x38(%rdi),%rcx
	sqe->addr3 = 0;
    a358:	48 c7 47 30 00 00 00 00 	movq   $0x0,0x30(%rdi)
	sqe->__pad2[0] = 0;
    a360:	48 89 ce             	mov    %rcx,%rsi
    a363:	48 c1 ee 03          	shr    $0x3,%rsi
    a367:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    a36e:	0f 85 fa 00 00 00    	jne    a46e <add_write_request+0x4ae>
	sqe->user_data = (unsigned long) data;
    a374:	48 8d 4f 20          	lea    0x20(%rdi),%rcx
	sqe->__pad2[0] = 0;
    a378:	48 c7 47 38 00 00 00 00 	movq   $0x0,0x38(%rdi)
	sqe->user_data = (unsigned long) data;
    a380:	48 89 ce             	mov    %rcx,%rsi
    a383:	48 c1 ee 03          	shr    $0x3,%rsi
    a387:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    a38e:	0f 85 ea 00 00 00    	jne    a47e <add_write_request+0x4be>
    a394:	48 89 57 20          	mov    %rdx,0x20(%rdi)
    io_uring_submit(ring);
    a398:	48 89 c7             	mov    %rax,%rdi
    a39b:	e8 c0 a2 ff ff       	call   4660 <io_uring_submit@plt>
}
    a3a0:	31 c0                	xor    %eax,%eax
    a3a2:	48 83 c4 08          	add    $0x8,%rsp
    a3a6:	c3                   	ret
    a3a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    a3b0:	49 c1 e8 03          	shr    $0x3,%r8
    a3b4:	45 0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%r8),%r9d
    a3bc:	49 89 f8             	mov    %rdi,%r8
    a3bf:	41 83 e0 07          	and    $0x7,%r8d
    a3c3:	41 83 c0 03          	add    $0x3,%r8d
    a3c7:	45 38 c8             	cmp    %r9b,%r8b
    a3ca:	7c 05                	jl     a3d1 <add_write_request+0x411>
    a3cc:	45 84 c9             	test   %r9b,%r9b
    a3cf:	75 7e                	jne    a44f <add_write_request+0x48f>
    a3d1:	8b 3f                	mov    (%rdi),%edi
    a3d3:	e9 9e fc ff ff       	jmp    a076 <add_write_request+0xb6>
	if (next - head <= sq->ring_entries) {
    a3d8:	4c 89 c7             	mov    %r8,%rdi
    a3db:	e8 70 a1 ff ff       	call   4550 <__asan_report_load4@plt>
	if (ring->flags & IORING_SETUP_SQE128)
    a3e0:	e8 6b a1 ff ff       	call   4550 <__asan_report_load4@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    a3e5:	e8 66 a1 ff ff       	call   4550 <__asan_report_load4@plt>
    req->event_type = EVENT_TYPE_WRITE;
    a3ea:	48 89 d7             	mov    %rdx,%rdi
    a3ed:	e8 ce a2 ff ff       	call   46c0 <__asan_report_store4@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    a3f2:	4c 89 d7             	mov    %r10,%rdi
    a3f5:	e8 56 a1 ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->flags = 0;
    a3fa:	48 89 cf             	mov    %rcx,%rdi
    a3fd:	e8 ce a3 ff ff       	call   47d0 <__asan_report_store1@plt>
	sqe->opcode = (__u8) op;
    a402:	e8 c9 a3 ff ff       	call   47d0 <__asan_report_store1@plt>
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    a407:	48 89 f7             	mov    %rsi,%rdi
    a40a:	e8 41 a1 ff ff       	call   4550 <__asan_report_load4@plt>
    a40f:	48 89 f7             	mov    %rsi,%rdi
    a412:	e8 39 a1 ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->file_index = 0;
    a417:	48 89 f7             	mov    %rsi,%rdi
    a41a:	e8 a1 a2 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->personality = 0;
    a41f:	48 89 f7             	mov    %rsi,%rdi
    a422:	e8 d9 a0 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->buf_index = 0;
    a427:	48 89 f7             	mov    %rsi,%rdi
    a42a:	e8 d1 a0 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->rw_flags = 0;
    a42f:	48 89 f7             	mov    %rsi,%rdi
    a432:	e8 89 a2 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->len = len;
    a437:	48 89 f7             	mov    %rsi,%rdi
    a43a:	e8 81 a2 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->fd = fd;
    a43f:	48 89 f7             	mov    %rsi,%rdi
    a442:	e8 79 a2 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->ioprio = 0;
    a447:	48 89 f7             	mov    %rsi,%rdi
    a44a:	e8 b1 a0 ff ff       	call   4500 <__asan_report_store2@plt>
		head = io_uring_smp_load_acquire(sq->khead);
    a44f:	e8 fc a0 ff ff       	call   4550 <__asan_report_load4@plt>
		head = IO_URING_READ_ONCE(*sq->khead);
    a454:	e8 f7 a0 ff ff       	call   4550 <__asan_report_load4@plt>
    a459:	48 89 c7             	mov    %rax,%rdi
    a45c:	e8 7f a0 ff ff       	call   44e0 <__asan_report_load8@plt>
	sqe->off = offset;
    a461:	48 89 cf             	mov    %rcx,%rdi
    a464:	e8 67 a2 ff ff       	call   46d0 <__asan_report_store8@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    a469:	e8 72 a0 ff ff       	call   44e0 <__asan_report_load8@plt>
	sqe->__pad2[0] = 0;
    a46e:	48 89 cf             	mov    %rcx,%rdi
    a471:	e8 5a a2 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->addr3 = 0;
    a476:	48 89 cf             	mov    %rcx,%rdi
    a479:	e8 52 a2 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->user_data = (unsigned long) data;
    a47e:	48 89 cf             	mov    %rcx,%rdi
    a481:	e8 4a a2 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->addr = (unsigned long) addr;
    a486:	48 89 cf             	mov    %rcx,%rdi
    a489:	e8 42 a2 ff ff       	call   46d0 <__asan_report_store8@plt>
    a48e:	66 90                	xchg   %ax,%ax

000000000000a490 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    a490:	f3 0f 1e fa          	endbr64
    a494:	41 55                	push   %r13
    a496:	41 89 fd             	mov    %edi,%r13d
	unsigned int head, next = sq->sqe_tail + 1;
    a499:	48 8d 7e 44          	lea    0x44(%rsi),%rdi
    a49d:	41 54                	push   %r12
    a49f:	48 89 f8             	mov    %rdi,%rax
    a4a2:	55                   	push   %rbp
    a4a3:	48 c1 e8 03          	shr    $0x3,%rax
    a4a7:	48 89 f5             	mov    %rsi,%rbp
    a4aa:	53                   	push   %rbx
    a4ab:	48 83 ec 08          	sub    $0x8,%rsp
    a4af:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    a4b6:	48 89 f8             	mov    %rdi,%rax
    a4b9:	83 e0 07             	and    $0x7,%eax
    a4bc:	83 c0 03             	add    $0x3,%eax
    a4bf:	38 d0                	cmp    %dl,%al
    a4c1:	7c 08                	jl     a4cb <add_read_request+0x3b>
    a4c3:	84 d2                	test   %dl,%dl
    a4c5:	0f 85 f4 03 00 00    	jne    a8bf <add_read_request+0x42f>
	if (ring->flags & IORING_SETUP_SQE128)
    a4cb:	48 8d bd c0 00 00 00 	lea    0xc0(%rbp),%rdi
	unsigned int head, next = sq->sqe_tail + 1;
    a4d2:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    a4d5:	48 89 fa             	mov    %rdi,%rdx
    a4d8:	48 c1 ea 03          	shr    $0x3,%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    a4dc:	83 c0 01             	add    $0x1,%eax
	if (ring->flags & IORING_SETUP_SQE128)
    a4df:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    a4e6:	84 d2                	test   %dl,%dl
    a4e8:	74 09                	je     a4f3 <add_read_request+0x63>
    a4ea:	80 fa 03             	cmp    $0x3,%dl
    a4ed:	0f 8e c7 03 00 00    	jle    a8ba <add_read_request+0x42a>
    a4f3:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    a4f9:	48 89 ee             	mov    %rbp,%rsi
    a4fc:	48 c1 ee 03          	shr    $0x3,%rsi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    a500:	89 ca                	mov    %ecx,%edx
    a502:	83 e2 02             	and    $0x2,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    a505:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    a50c:	0f 85 0a 04 00 00    	jne    a91c <add_read_request+0x48c>
    a512:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    a516:	85 d2                	test   %edx,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    a518:	48 89 fa             	mov    %rdi,%rdx
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    a51b:	0f 85 6f 03 00 00    	jne    a890 <add_read_request+0x400>
		head = IO_URING_READ_ONCE(*sq->khead);
    a521:	48 c1 ea 03          	shr    $0x3,%rdx
    a525:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    a52c:	48 89 fa             	mov    %rdi,%rdx
    a52f:	83 e2 07             	and    $0x7,%edx
    a532:	83 c2 03             	add    $0x3,%edx
    a535:	40 38 f2             	cmp    %sil,%dl
    a538:	7c 09                	jl     a543 <add_read_request+0xb3>
    a53a:	40 84 f6             	test   %sil,%sil
    a53d:	0f 85 cf 03 00 00    	jne    a912 <add_read_request+0x482>
    a543:	8b 17                	mov    (%rdi),%edx
	if (next - head <= sq->ring_entries) {
    a545:	48 8d 7d 5c          	lea    0x5c(%rbp),%rdi
    a549:	41 89 c0             	mov    %eax,%r8d
    a54c:	41 29 d0             	sub    %edx,%r8d
    a54f:	48 89 fa             	mov    %rdi,%rdx
    a552:	48 c1 ea 03          	shr    $0x3,%rdx
    a556:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    a55d:	48 89 fa             	mov    %rdi,%rdx
    a560:	83 e2 07             	and    $0x7,%edx
    a563:	83 c2 03             	add    $0x3,%edx
    a566:	40 38 f2             	cmp    %sil,%dl
    a569:	7c 09                	jl     a574 <add_read_request+0xe4>
    a56b:	40 84 f6             	test   %sil,%sil
    a56e:	0f 85 41 03 00 00    	jne    a8b5 <add_read_request+0x425>
    a574:	44 39 45 5c          	cmp    %r8d,0x5c(%rbp)
    a578:	0f 82 31 a3 ff ff    	jb     48af <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    a57e:	48 8d 7d 38          	lea    0x38(%rbp),%rdi
    a582:	48 89 fa             	mov    %rdi,%rdx
    a585:	48 c1 ea 03          	shr    $0x3,%rdx
    a589:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    a590:	0f 85 8e 03 00 00    	jne    a924 <add_read_request+0x494>
    a596:	48 8d 7d 58          	lea    0x58(%rbp),%rdi
    a59a:	48 8b 5d 38          	mov    0x38(%rbp),%rbx
    a59e:	8b 55 44             	mov    0x44(%rbp),%edx
    a5a1:	48 89 fe             	mov    %rdi,%rsi
    a5a4:	48 c1 ee 03          	shr    $0x3,%rsi
    a5a8:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    a5af:	40 84 f6             	test   %sil,%sil
    a5b2:	74 0a                	je     a5be <add_read_request+0x12e>
    a5b4:	40 80 fe 03          	cmp    $0x3,%sil
    a5b8:	0f 8e 0e 03 00 00    	jle    a8cc <add_read_request+0x43c>
	if (ring->flags & IORING_SETUP_SQE128)
    a5be:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    a5c1:	23 55 58             	and    0x58(%rbp),%edx
		sq->sqe_tail = next;
    a5c4:	89 45 44             	mov    %eax,0x44(%rbp)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    a5c7:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    a5cc:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    a5cf:	d3 e2                	shl    %cl,%edx
    a5d1:	48 c1 e2 06          	shl    $0x6,%rdx
    a5d5:	48 01 d3             	add    %rdx,%rbx
    a5d8:	e8 b3 9f ff ff       	call   4590 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    a5dd:	bf 00 20 00 00       	mov    $0x2000,%edi
    a5e2:	be 01 00 00 00       	mov    $0x1,%esi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    a5e7:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    a5ea:	e8 71 9e ff ff       	call   4460 <calloc@plt>
    a5ef:	49 8d 7c 24 10       	lea    0x10(%r12),%rdi
    a5f4:	48 89 fa             	mov    %rdi,%rdx
    a5f7:	48 c1 ea 03          	shr    $0x3,%rdx
    a5fb:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    a602:	0f 85 43 03 00 00    	jne    a94b <add_read_request+0x4bb>
    a608:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    req->iov[0].iov_len = READ_SZ;
    a60d:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    a612:	48 89 c2             	mov    %rax,%rdx
    a615:	48 c1 ea 03          	shr    $0x3,%rdx
    a619:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    a620:	0f 85 1d 03 00 00    	jne    a943 <add_read_request+0x4b3>
    a626:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    a62f:	4c 89 e0             	mov    %r12,%rax
    a632:	48 c1 e8 03          	shr    $0x3,%rax
    a636:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    a63d:	84 c0                	test   %al,%al
    a63f:	74 08                	je     a649 <add_read_request+0x1b9>
    a641:	3c 03                	cmp    $0x3,%al
    a643:	0f 8e 7b 02 00 00    	jle    a8c4 <add_read_request+0x434>
    req->client_socket = client_socket;
    a649:	49 8d 54 24 08       	lea    0x8(%r12),%rdx
    req->event_type = EVENT_TYPE_READ;
    a64e:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    req->client_socket = client_socket;
    a656:	48 89 d0             	mov    %rdx,%rax
    a659:	48 c1 e8 03          	shr    $0x3,%rax
    a65d:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    a664:	84 c0                	test   %al,%al
    a666:	74 08                	je     a670 <add_read_request+0x1e0>
    a668:	3c 03                	cmp    $0x3,%al
    a66a:	0f 8e 79 02 00 00    	jle    a8e9 <add_read_request+0x459>
	sqe->opcode = (__u8) op;
    a670:	48 89 d8             	mov    %rbx,%rax
    a673:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    a678:	48 c1 e8 03          	shr    $0x3,%rax
    a67c:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    a683:	84 c0                	test   %al,%al
    a685:	74 06                	je     a68d <add_read_request+0x1fd>
    a687:	0f 8e 54 02 00 00    	jle    a8e1 <add_read_request+0x451>
	sqe->flags = 0;
    a68d:	48 8d 43 01          	lea    0x1(%rbx),%rax
	sqe->opcode = (__u8) op;
    a691:	c6 03 01             	movb   $0x1,(%rbx)
	sqe->flags = 0;
    a694:	48 89 c2             	mov    %rax,%rdx
    a697:	48 89 c1             	mov    %rax,%rcx
    a69a:	48 c1 ea 03          	shr    $0x3,%rdx
    a69e:	83 e1 07             	and    $0x7,%ecx
    a6a1:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    a6a8:	38 ca                	cmp    %cl,%dl
    a6aa:	7f 08                	jg     a6b4 <add_read_request+0x224>
    a6ac:	84 d2                	test   %dl,%dl
    a6ae:	0f 85 25 02 00 00    	jne    a8d9 <add_read_request+0x449>
	sqe->ioprio = 0;
    a6b4:	48 8d 53 02          	lea    0x2(%rbx),%rdx
	sqe->flags = 0;
    a6b8:	c6 43 01 00          	movb   $0x0,0x1(%rbx)
	sqe->ioprio = 0;
    a6bc:	48 89 d0             	mov    %rdx,%rax
    a6bf:	48 c1 e8 03          	shr    $0x3,%rax
    a6c3:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    a6ca:	48 89 d0             	mov    %rdx,%rax
    a6cd:	83 e0 07             	and    $0x7,%eax
    a6d0:	83 c0 01             	add    $0x1,%eax
    a6d3:	38 c8                	cmp    %cl,%al
    a6d5:	7c 08                	jl     a6df <add_read_request+0x24f>
    a6d7:	84 c9                	test   %cl,%cl
    a6d9:	0f 85 f2 01 00 00    	jne    a8d1 <add_read_request+0x441>
	sqe->fd = fd;
    a6df:	48 8d 53 04          	lea    0x4(%rbx),%rdx
	sqe->ioprio = 0;
    a6e3:	31 c9                	xor    %ecx,%ecx
	sqe->fd = fd;
    a6e5:	48 89 d0             	mov    %rdx,%rax
	sqe->ioprio = 0;
    a6e8:	66 89 4b 02          	mov    %cx,0x2(%rbx)
	sqe->fd = fd;
    a6ec:	48 c1 e8 03          	shr    $0x3,%rax
    a6f0:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    a6f7:	48 89 d0             	mov    %rdx,%rax
    a6fa:	83 e0 07             	and    $0x7,%eax
    a6fd:	83 c0 03             	add    $0x3,%eax
    a700:	38 c8                	cmp    %cl,%al
    a702:	7c 08                	jl     a70c <add_read_request+0x27c>
    a704:	84 c9                	test   %cl,%cl
    a706:	0f 85 fe 01 00 00    	jne    a90a <add_read_request+0x47a>
	sqe->off = offset;
    a70c:	48 8d 43 08          	lea    0x8(%rbx),%rax
	sqe->fd = fd;
    a710:	44 89 6b 04          	mov    %r13d,0x4(%rbx)
	sqe->off = offset;
    a714:	48 89 c2             	mov    %rax,%rdx
    a717:	48 c1 ea 03          	shr    $0x3,%rdx
    a71b:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    a722:	0f 85 13 02 00 00    	jne    a93b <add_read_request+0x4ab>
	sqe->addr = (unsigned long) addr;
    a728:	48 8d 43 10          	lea    0x10(%rbx),%rax
	sqe->off = offset;
    a72c:	48 c7 43 08 00 00 00 00 	movq   $0x0,0x8(%rbx)
	sqe->addr = (unsigned long) addr;
    a734:	48 89 c2             	mov    %rax,%rdx
    a737:	48 c1 ea 03          	shr    $0x3,%rdx
    a73b:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    a742:	0f 85 e1 01 00 00    	jne    a929 <add_read_request+0x499>
    a748:	48 89 7b 10          	mov    %rdi,0x10(%rbx)
	sqe->len = len;
    a74c:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    a750:	48 89 f8             	mov    %rdi,%rax
    a753:	48 c1 e8 03          	shr    $0x3,%rax
    a757:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    a75e:	84 c0                	test   %al,%al
    a760:	74 08                	je     a76a <add_read_request+0x2da>
    a762:	3c 03                	cmp    $0x3,%al
    a764:	0f 8e 9b 01 00 00    	jle    a905 <add_read_request+0x475>
	sqe->rw_flags = 0;
    a76a:	48 8d 7b 1c          	lea    0x1c(%rbx),%rdi
	sqe->len = len;
    a76e:	c7 43 18 01 00 00 00 	movl   $0x1,0x18(%rbx)
	sqe->rw_flags = 0;
    a775:	48 89 f8             	mov    %rdi,%rax
    a778:	48 c1 e8 03          	shr    $0x3,%rax
    a77c:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    a783:	48 89 f8             	mov    %rdi,%rax
    a786:	83 e0 07             	and    $0x7,%eax
    a789:	83 c0 03             	add    $0x3,%eax
    a78c:	38 d0                	cmp    %dl,%al
    a78e:	7c 08                	jl     a798 <add_read_request+0x308>
    a790:	84 d2                	test   %dl,%dl
    a792:	0f 85 68 01 00 00    	jne    a900 <add_read_request+0x470>
	sqe->buf_index = 0;
    a798:	48 8d 7b 28          	lea    0x28(%rbx),%rdi
	sqe->rw_flags = 0;
    a79c:	c7 43 1c 00 00 00 00 	movl   $0x0,0x1c(%rbx)
	sqe->buf_index = 0;
    a7a3:	48 89 f8             	mov    %rdi,%rax
    a7a6:	48 c1 e8 03          	shr    $0x3,%rax
    a7aa:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    a7b1:	84 c0                	test   %al,%al
    a7b3:	74 08                	je     a7bd <add_read_request+0x32d>
    a7b5:	3c 01                	cmp    $0x1,%al
    a7b7:	0f 8e 3e 01 00 00    	jle    a8fb <add_read_request+0x46b>
	sqe->personality = 0;
    a7bd:	48 8d 7b 2a          	lea    0x2a(%rbx),%rdi
	sqe->buf_index = 0;
    a7c1:	31 d2                	xor    %edx,%edx
	sqe->personality = 0;
    a7c3:	48 89 f8             	mov    %rdi,%rax
	sqe->buf_index = 0;
    a7c6:	66 89 53 28          	mov    %dx,0x28(%rbx)
	sqe->personality = 0;
    a7ca:	48 c1 e8 03          	shr    $0x3,%rax
    a7ce:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    a7d5:	48 89 f8             	mov    %rdi,%rax
    a7d8:	83 e0 07             	and    $0x7,%eax
    a7db:	83 c0 01             	add    $0x1,%eax
    a7de:	38 d0                	cmp    %dl,%al
    a7e0:	7c 08                	jl     a7ea <add_read_request+0x35a>
    a7e2:	84 d2                	test   %dl,%dl
    a7e4:	0f 85 0c 01 00 00    	jne    a8f6 <add_read_request+0x466>
    a7ea:	31 c0                	xor    %eax,%eax
	sqe->file_index = 0;
    a7ec:	48 8d 7b 2c          	lea    0x2c(%rbx),%rdi
	sqe->personality = 0;
    a7f0:	66 89 43 2a          	mov    %ax,0x2a(%rbx)
	sqe->file_index = 0;
    a7f4:	48 89 f8             	mov    %rdi,%rax
    a7f7:	48 c1 e8 03          	shr    $0x3,%rax
    a7fb:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    a802:	48 89 f8             	mov    %rdi,%rax
    a805:	83 e0 07             	and    $0x7,%eax
    a808:	83 c0 03             	add    $0x3,%eax
    a80b:	38 d0                	cmp    %dl,%al
    a80d:	7c 08                	jl     a817 <add_read_request+0x387>
    a80f:	84 d2                	test   %dl,%dl
    a811:	0f 85 da 00 00 00    	jne    a8f1 <add_read_request+0x461>
	sqe->addr3 = 0;
    a817:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
	sqe->file_index = 0;
    a81b:	c7 43 2c 00 00 00 00 	movl   $0x0,0x2c(%rbx)
	sqe->addr3 = 0;
    a822:	48 89 f8             	mov    %rdi,%rax
    a825:	48 c1 e8 03          	shr    $0x3,%rax
    a829:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    a830:	0f 85 00 01 00 00    	jne    a936 <add_read_request+0x4a6>
	sqe->__pad2[0] = 0;
    a836:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
	sqe->addr3 = 0;
    a83a:	48 c7 43 30 00 00 00 00 	movq   $0x0,0x30(%rbx)
	sqe->__pad2[0] = 0;
    a842:	48 89 f8             	mov    %rdi,%rax
    a845:	48 c1 e8 03          	shr    $0x3,%rax
    a849:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    a850:	0f 85 db 00 00 00    	jne    a931 <add_read_request+0x4a1>
	sqe->user_data = (unsigned long) data;
    a856:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
	sqe->__pad2[0] = 0;
    a85a:	48 c7 43 38 00 00 00 00 	movq   $0x0,0x38(%rbx)
	sqe->user_data = (unsigned long) data;
    a862:	48 89 f8             	mov    %rdi,%rax
    a865:	48 c1 e8 03          	shr    $0x3,%rax
    a869:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    a870:	0f 85 da 00 00 00    	jne    a950 <add_read_request+0x4c0>
    a876:	4c 89 63 20          	mov    %r12,0x20(%rbx)
    io_uring_submit(ring);
    a87a:	48 89 ef             	mov    %rbp,%rdi
    a87d:	e8 de 9d ff ff       	call   4660 <io_uring_submit@plt>
}
    a882:	48 83 c4 08          	add    $0x8,%rsp
    a886:	31 c0                	xor    %eax,%eax
    a888:	5b                   	pop    %rbx
    a889:	5d                   	pop    %rbp
    a88a:	41 5c                	pop    %r12
    a88c:	41 5d                	pop    %r13
    a88e:	c3                   	ret
    a88f:	90                   	nop
		head = io_uring_smp_load_acquire(sq->khead);
    a890:	48 c1 ea 03          	shr    $0x3,%rdx
    a894:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    a89b:	48 89 fa             	mov    %rdi,%rdx
    a89e:	83 e2 07             	and    $0x7,%edx
    a8a1:	83 c2 03             	add    $0x3,%edx
    a8a4:	40 38 f2             	cmp    %sil,%dl
    a8a7:	7c 05                	jl     a8ae <add_read_request+0x41e>
    a8a9:	40 84 f6             	test   %sil,%sil
    a8ac:	75 69                	jne    a917 <add_read_request+0x487>
    a8ae:	8b 17                	mov    (%rdi),%edx
    a8b0:	e9 90 fc ff ff       	jmp    a545 <add_read_request+0xb5>
	if (next - head <= sq->ring_entries) {
    a8b5:	e8 96 9c ff ff       	call   4550 <__asan_report_load4@plt>
	if (ring->flags & IORING_SETUP_SQE128)
    a8ba:	e8 91 9c ff ff       	call   4550 <__asan_report_load4@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    a8bf:	e8 8c 9c ff ff       	call   4550 <__asan_report_load4@plt>
    req->event_type = EVENT_TYPE_READ;
    a8c4:	4c 89 e7             	mov    %r12,%rdi
    a8c7:	e8 f4 9d ff ff       	call   46c0 <__asan_report_store4@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    a8cc:	e8 7f 9c ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->ioprio = 0;
    a8d1:	48 89 d7             	mov    %rdx,%rdi
    a8d4:	e8 27 9c ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->flags = 0;
    a8d9:	48 89 c7             	mov    %rax,%rdi
    a8dc:	e8 ef 9e ff ff       	call   47d0 <__asan_report_store1@plt>
	sqe->opcode = (__u8) op;
    a8e1:	48 89 df             	mov    %rbx,%rdi
    a8e4:	e8 e7 9e ff ff       	call   47d0 <__asan_report_store1@plt>
    req->client_socket = client_socket;
    a8e9:	48 89 d7             	mov    %rdx,%rdi
    a8ec:	e8 cf 9d ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->file_index = 0;
    a8f1:	e8 ca 9d ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->personality = 0;
    a8f6:	e8 05 9c ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->buf_index = 0;
    a8fb:	e8 00 9c ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->rw_flags = 0;
    a900:	e8 bb 9d ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->len = len;
    a905:	e8 b6 9d ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->fd = fd;
    a90a:	48 89 d7             	mov    %rdx,%rdi
    a90d:	e8 ae 9d ff ff       	call   46c0 <__asan_report_store4@plt>
		head = IO_URING_READ_ONCE(*sq->khead);
    a912:	e8 39 9c ff ff       	call   4550 <__asan_report_load4@plt>
		head = io_uring_smp_load_acquire(sq->khead);
    a917:	e8 34 9c ff ff       	call   4550 <__asan_report_load4@plt>
		head = IO_URING_READ_ONCE(*sq->khead);
    a91c:	48 89 ef             	mov    %rbp,%rdi
    a91f:	e8 bc 9b ff ff       	call   44e0 <__asan_report_load8@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    a924:	e8 b7 9b ff ff       	call   44e0 <__asan_report_load8@plt>
	sqe->addr = (unsigned long) addr;
    a929:	48 89 c7             	mov    %rax,%rdi
    a92c:	e8 9f 9d ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->__pad2[0] = 0;
    a931:	e8 9a 9d ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->addr3 = 0;
    a936:	e8 95 9d ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->off = offset;
    a93b:	48 89 c7             	mov    %rax,%rdi
    a93e:	e8 8d 9d ff ff       	call   46d0 <__asan_report_store8@plt>
    req->iov[0].iov_len = READ_SZ;
    a943:	48 89 c7             	mov    %rax,%rdi
    a946:	e8 85 9d ff ff       	call   46d0 <__asan_report_store8@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    a94b:	e8 80 9d ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->user_data = (unsigned long) data;
    a950:	e8 7b 9d ff ff       	call   46d0 <__asan_report_store8@plt>
    a955:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

000000000000a960 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    a960:	f3 0f 1e fa          	endbr64
    a964:	41 56                	push   %r14
    a966:	41 89 f6             	mov    %esi,%r14d
    a969:	41 55                	push   %r13
    a96b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    a96e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    a973:	41 54                	push   %r12
    a975:	55                   	push   %rbp
    a976:	53                   	push   %rbx
    a977:	48 89 d3             	mov    %rdx,%rbx
    void *buf = malloc(size);
    a97a:	e8 11 9c ff ff       	call   4590 <malloc@plt>
    if (!buf) {
    a97f:	48 85 c0             	test   %rax,%rax
    a982:	0f 84 83 04 00 00    	je     ae0b <_send_static_string_content+0x4ab>
    a988:	48 89 c5             	mov    %rax,%rbp
    unsigned long slen = strlen(str);
    a98b:	4c 89 ef             	mov    %r13,%rdi
    a98e:	e8 4d 9c ff ff       	call   45e0 <strlen@plt>
    req->iovec_count = 1;
    a993:	48 8d 7d 04          	lea    0x4(%rbp),%rdi
    unsigned long slen = strlen(str);
    a997:	49 89 c4             	mov    %rax,%r12
    req->iovec_count = 1;
    a99a:	48 89 f8             	mov    %rdi,%rax
    a99d:	48 c1 e8 03          	shr    $0x3,%rax
    a9a1:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    a9a8:	48 89 f8             	mov    %rdi,%rax
    a9ab:	83 e0 07             	and    $0x7,%eax
    a9ae:	83 c0 03             	add    $0x3,%eax
    a9b1:	38 d0                	cmp    %dl,%al
    a9b3:	7c 08                	jl     a9bd <_send_static_string_content+0x5d>
    a9b5:	84 d2                	test   %dl,%dl
    a9b7:	0f 85 20 04 00 00    	jne    addd <_send_static_string_content+0x47d>
    req->client_socket = client_socket;
    a9bd:	48 8d 7d 08          	lea    0x8(%rbp),%rdi
    req->iovec_count = 1;
    a9c1:	c7 45 04 01 00 00 00 	movl   $0x1,0x4(%rbp)
    req->client_socket = client_socket;
    a9c8:	48 89 f8             	mov    %rdi,%rax
    a9cb:	48 c1 e8 03          	shr    $0x3,%rax
    a9cf:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    a9d6:	84 c0                	test   %al,%al
    a9d8:	74 08                	je     a9e2 <_send_static_string_content+0x82>
    a9da:	3c 03                	cmp    $0x3,%al
    a9dc:	0f 8e 00 04 00 00    	jle    ade2 <_send_static_string_content+0x482>
    a9e2:	44 89 75 08          	mov    %r14d,0x8(%rbp)
    void *buf = malloc(size);
    a9e6:	4c 89 e7             	mov    %r12,%rdi
    a9e9:	e8 a2 9b ff ff       	call   4590 <malloc@plt>
    a9ee:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    a9f1:	48 85 c0             	test   %rax,%rax
    a9f4:	0f 84 58 04 00 00    	je     ae52 <_send_static_string_content+0x4f2>
    req->iov[0].iov_base = zh_malloc(slen);
    a9fa:	4c 8d 75 10          	lea    0x10(%rbp),%r14
    a9fe:	4c 89 f0             	mov    %r14,%rax
    aa01:	48 c1 e8 03          	shr    $0x3,%rax
    aa05:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    aa0c:	0f 85 f1 03 00 00    	jne    ae03 <_send_static_string_content+0x4a3>
    req->iov[0].iov_len = slen;
    aa12:	48 8d 45 18          	lea    0x18(%rbp),%rax
    req->iov[0].iov_base = zh_malloc(slen);
    aa16:	48 89 7d 10          	mov    %rdi,0x10(%rbp)
    req->iov[0].iov_len = slen;
    aa1a:	48 89 c2             	mov    %rax,%rdx
    aa1d:	48 c1 ea 03          	shr    $0x3,%rdx
    aa21:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    aa28:	0f 85 c8 03 00 00    	jne    adf6 <_send_static_string_content+0x496>
    aa2e:	4c 89 65 18          	mov    %r12,0x18(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    aa32:	4c 89 e2             	mov    %r12,%rdx
    aa35:	4c 89 ee             	mov    %r13,%rsi
    aa38:	e8 83 9a ff ff       	call   44c0 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    aa3d:	48 8d 7b 44          	lea    0x44(%rbx),%rdi
    aa41:	48 89 f8             	mov    %rdi,%rax
    aa44:	48 c1 e8 03          	shr    $0x3,%rax
    aa48:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    aa4f:	48 89 f8             	mov    %rdi,%rax
    aa52:	83 e0 07             	and    $0x7,%eax
    aa55:	83 c0 03             	add    $0x3,%eax
    aa58:	38 d0                	cmp    %dl,%al
    aa5a:	7c 08                	jl     aa64 <_send_static_string_content+0x104>
    aa5c:	84 d2                	test   %dl,%dl
    aa5e:	0f 85 74 03 00 00    	jne    add8 <_send_static_string_content+0x478>
	if (ring->flags & IORING_SETUP_SQE128)
    aa64:	48 8d bb c0 00 00 00 	lea    0xc0(%rbx),%rdi
	unsigned int head, next = sq->sqe_tail + 1;
    aa6b:	8b 43 44             	mov    0x44(%rbx),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    aa6e:	48 89 fa             	mov    %rdi,%rdx
    aa71:	48 c1 ea 03          	shr    $0x3,%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    aa75:	83 c0 01             	add    $0x1,%eax
	if (ring->flags & IORING_SETUP_SQE128)
    aa78:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    aa7f:	84 d2                	test   %dl,%dl
    aa81:	74 09                	je     aa8c <_send_static_string_content+0x12c>
    aa83:	80 fa 03             	cmp    $0x3,%dl
    aa86:	0f 8e 5b 03 00 00    	jle    ade7 <_send_static_string_content+0x487>
    aa8c:	8b 8b c0 00 00 00    	mov    0xc0(%rbx),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    aa92:	48 89 da             	mov    %rbx,%rdx
    aa95:	48 c1 ea 03          	shr    $0x3,%rdx
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    aa99:	f6 c1 02             	test   $0x2,%cl
    aa9c:	0f 85 fe 02 00 00    	jne    ada0 <_send_static_string_content+0x440>
		head = IO_URING_READ_ONCE(*sq->khead);
    aaa2:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    aaa9:	0f 85 41 04 00 00    	jne    aef0 <_send_static_string_content+0x590>
    aaaf:	48 8b 3b             	mov    (%rbx),%rdi
    aab2:	48 89 fa             	mov    %rdi,%rdx
    aab5:	48 c1 ea 03          	shr    $0x3,%rdx
    aab9:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    aac0:	48 89 fa             	mov    %rdi,%rdx
    aac3:	83 e2 07             	and    $0x7,%edx
    aac6:	83 c2 03             	add    $0x3,%edx
    aac9:	40 38 f2             	cmp    %sil,%dl
    aacc:	7c 09                	jl     aad7 <_send_static_string_content+0x177>
    aace:	40 84 f6             	test   %sil,%sil
    aad1:	0f 85 15 03 00 00    	jne    adec <_send_static_string_content+0x48c>
    aad7:	8b 17                	mov    (%rdi),%edx
	if (next - head <= sq->ring_entries) {
    aad9:	48 8d 7b 5c          	lea    0x5c(%rbx),%rdi
    aadd:	41 89 c0             	mov    %eax,%r8d
    aae0:	41 29 d0             	sub    %edx,%r8d
    aae3:	48 89 fa             	mov    %rdi,%rdx
    aae6:	48 c1 ea 03          	shr    $0x3,%rdx
    aaea:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    aaf1:	48 89 fa             	mov    %rdi,%rdx
    aaf4:	83 e2 07             	and    $0x7,%edx
    aaf7:	83 c2 03             	add    $0x3,%edx
    aafa:	40 38 f2             	cmp    %sil,%dl
    aafd:	7c 09                	jl     ab08 <_send_static_string_content+0x1a8>
    aaff:	40 84 f6             	test   %sil,%sil
    ab02:	0f 85 f6 02 00 00    	jne    adfe <_send_static_string_content+0x49e>
    ab08:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    ab0c:	0f 82 5d 9e ff ff    	jb     496f <_send_static_string_content.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    ab12:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    ab16:	48 89 fa             	mov    %rdi,%rdx
    ab19:	48 c1 ea 03          	shr    $0x3,%rdx
    ab1d:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    ab24:	0f 85 69 03 00 00    	jne    ae93 <_send_static_string_content+0x533>
    ab2a:	4c 8d 43 58          	lea    0x58(%rbx),%r8
    ab2e:	48 8b 7b 38          	mov    0x38(%rbx),%rdi
    ab32:	8b 53 44             	mov    0x44(%rbx),%edx
    ab35:	4c 89 c6             	mov    %r8,%rsi
    ab38:	48 c1 ee 03          	shr    $0x3,%rsi
    ab3c:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    ab43:	40 84 f6             	test   %sil,%sil
    ab46:	74 0a                	je     ab52 <_send_static_string_content+0x1f2>
    ab48:	40 80 fe 03          	cmp    $0x3,%sil
    ab4c:	0f 8e 46 03 00 00    	jle    ae98 <_send_static_string_content+0x538>
		sq->sqe_tail = next;
    ab52:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    ab55:	c1 e9 0a             	shr    $0xa,%ecx
    req->event_type = EVENT_TYPE_WRITE;
    ab58:	48 89 e8             	mov    %rbp,%rax
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    ab5b:	23 53 58             	and    0x58(%rbx),%edx
	if (ring->flags & IORING_SETUP_SQE128)
    ab5e:	83 e1 01             	and    $0x1,%ecx
    ab61:	48 c1 e8 03          	shr    $0x3,%rax
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    ab65:	d3 e2                	shl    %cl,%edx
    ab67:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    ab6e:	48 c1 e2 06          	shl    $0x6,%rdx
    ab72:	48 01 d7             	add    %rdx,%rdi
    ab75:	84 c0                	test   %al,%al
    ab77:	74 08                	je     ab81 <_send_static_string_content+0x221>
    ab79:	3c 03                	cmp    $0x3,%al
    ab7b:	0f 8e ed 02 00 00    	jle    ae6e <_send_static_string_content+0x50e>
	sqe->opcode = (__u8) op;
    ab81:	48 89 f8             	mov    %rdi,%rax
    ab84:	c7 45 00 02 00 00 00 	movl   $0x2,0x0(%rbp)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    ab8b:	8b 75 04             	mov    0x4(%rbp),%esi
    ab8e:	48 c1 e8 03          	shr    $0x3,%rax
    ab92:	44 8b 45 08          	mov    0x8(%rbp),%r8d
    ab96:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    ab9d:	84 c0                	test   %al,%al
    ab9f:	74 06                	je     aba7 <_send_static_string_content+0x247>
    aba1:	0f 8e cf 02 00 00    	jle    ae76 <_send_static_string_content+0x516>
	sqe->flags = 0;
    aba7:	48 8d 47 01          	lea    0x1(%rdi),%rax
	sqe->opcode = (__u8) op;
    abab:	c6 07 02             	movb   $0x2,(%rdi)
	sqe->flags = 0;
    abae:	48 89 c2             	mov    %rax,%rdx
    abb1:	48 89 c1             	mov    %rax,%rcx
    abb4:	48 c1 ea 03          	shr    $0x3,%rdx
    abb8:	83 e1 07             	and    $0x7,%ecx
    abbb:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    abc2:	38 ca                	cmp    %cl,%dl
    abc4:	7f 08                	jg     abce <_send_static_string_content+0x26e>
    abc6:	84 d2                	test   %dl,%dl
    abc8:	0f 85 ad 02 00 00    	jne    ae7b <_send_static_string_content+0x51b>
	sqe->ioprio = 0;
    abce:	48 8d 57 02          	lea    0x2(%rdi),%rdx
	sqe->flags = 0;
    abd2:	c6 47 01 00          	movb   $0x0,0x1(%rdi)
	sqe->ioprio = 0;
    abd6:	48 89 d0             	mov    %rdx,%rax
    abd9:	48 c1 e8 03          	shr    $0x3,%rax
    abdd:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    abe4:	48 89 d0             	mov    %rdx,%rax
    abe7:	83 e0 07             	and    $0x7,%eax
    abea:	83 c0 01             	add    $0x1,%eax
    abed:	38 c8                	cmp    %cl,%al
    abef:	7c 08                	jl     abf9 <_send_static_string_content+0x299>
    abf1:	84 c9                	test   %cl,%cl
    abf3:	0f 85 b7 02 00 00    	jne    aeb0 <_send_static_string_content+0x550>
	sqe->fd = fd;
    abf9:	48 8d 57 04          	lea    0x4(%rdi),%rdx
	sqe->ioprio = 0;
    abfd:	31 c9                	xor    %ecx,%ecx
	sqe->fd = fd;
    abff:	48 89 d0             	mov    %rdx,%rax
	sqe->ioprio = 0;
    ac02:	66 89 4f 02          	mov    %cx,0x2(%rdi)
	sqe->fd = fd;
    ac06:	48 c1 e8 03          	shr    $0x3,%rax
    ac0a:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    ac11:	48 89 d0             	mov    %rdx,%rax
    ac14:	83 e0 07             	and    $0x7,%eax
    ac17:	83 c0 03             	add    $0x3,%eax
    ac1a:	38 c8                	cmp    %cl,%al
    ac1c:	7c 08                	jl     ac26 <_send_static_string_content+0x2c6>
    ac1e:	84 c9                	test   %cl,%cl
    ac20:	0f 85 92 02 00 00    	jne    aeb8 <_send_static_string_content+0x558>
	sqe->off = offset;
    ac26:	48 8d 47 08          	lea    0x8(%rdi),%rax
	sqe->fd = fd;
    ac2a:	44 89 47 04          	mov    %r8d,0x4(%rdi)
	sqe->off = offset;
    ac2e:	48 89 c2             	mov    %rax,%rdx
    ac31:	48 c1 ea 03          	shr    $0x3,%rdx
    ac35:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    ac3c:	0f 85 7e 02 00 00    	jne    aec0 <_send_static_string_content+0x560>
	sqe->addr = (unsigned long) addr;
    ac42:	48 8d 47 10          	lea    0x10(%rdi),%rax
	sqe->off = offset;
    ac46:	48 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%rdi)
	sqe->addr = (unsigned long) addr;
    ac4e:	48 89 c2             	mov    %rax,%rdx
    ac51:	48 c1 ea 03          	shr    $0x3,%rdx
    ac55:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    ac5c:	0f 85 66 02 00 00    	jne    aec8 <_send_static_string_content+0x568>
	sqe->len = len;
    ac62:	48 8d 57 18          	lea    0x18(%rdi),%rdx
	sqe->addr = (unsigned long) addr;
    ac66:	4c 89 77 10          	mov    %r14,0x10(%rdi)
	sqe->len = len;
    ac6a:	48 89 d0             	mov    %rdx,%rax
    ac6d:	48 c1 e8 03          	shr    $0x3,%rax
    ac71:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    ac78:	84 c0                	test   %al,%al
    ac7a:	74 08                	je     ac84 <_send_static_string_content+0x324>
    ac7c:	3c 03                	cmp    $0x3,%al
    ac7e:	0f 8e 4c 02 00 00    	jle    aed0 <_send_static_string_content+0x570>
	sqe->rw_flags = 0;
    ac84:	48 8d 57 1c          	lea    0x1c(%rdi),%rdx
	sqe->len = len;
    ac88:	89 77 18             	mov    %esi,0x18(%rdi)
	sqe->rw_flags = 0;
    ac8b:	48 89 d0             	mov    %rdx,%rax
    ac8e:	48 c1 e8 03          	shr    $0x3,%rax
    ac92:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    ac99:	48 89 d0             	mov    %rdx,%rax
    ac9c:	83 e0 07             	and    $0x7,%eax
    ac9f:	83 c0 03             	add    $0x3,%eax
    aca2:	38 c8                	cmp    %cl,%al
    aca4:	7c 08                	jl     acae <_send_static_string_content+0x34e>
    aca6:	84 c9                	test   %cl,%cl
    aca8:	0f 85 f2 01 00 00    	jne    aea0 <_send_static_string_content+0x540>
	sqe->buf_index = 0;
    acae:	48 8d 57 28          	lea    0x28(%rdi),%rdx
	sqe->rw_flags = 0;
    acb2:	c7 47 1c 00 00 00 00 	movl   $0x0,0x1c(%rdi)
	sqe->buf_index = 0;
    acb9:	48 89 d0             	mov    %rdx,%rax
    acbc:	48 c1 e8 03          	shr    $0x3,%rax
    acc0:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    acc7:	84 c0                	test   %al,%al
    acc9:	74 08                	je     acd3 <_send_static_string_content+0x373>
    accb:	3c 01                	cmp    $0x1,%al
    accd:	0f 8e d5 01 00 00    	jle    aea8 <_send_static_string_content+0x548>
    acd3:	31 d2                	xor    %edx,%edx
    acd5:	66 89 57 28          	mov    %dx,0x28(%rdi)
	sqe->personality = 0;
    acd9:	48 8d 57 2a          	lea    0x2a(%rdi),%rdx
    acdd:	48 89 d0             	mov    %rdx,%rax
    ace0:	48 c1 e8 03          	shr    $0x3,%rax
    ace4:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    aceb:	48 89 d0             	mov    %rdx,%rax
    acee:	83 e0 07             	and    $0x7,%eax
    acf1:	83 c0 01             	add    $0x1,%eax
    acf4:	38 c8                	cmp    %cl,%al
    acf6:	7c 08                	jl     ad00 <_send_static_string_content+0x3a0>
    acf8:	84 c9                	test   %cl,%cl
    acfa:	0f 85 83 01 00 00    	jne    ae83 <_send_static_string_content+0x523>
    ad00:	31 c0                	xor    %eax,%eax
	sqe->file_index = 0;
    ad02:	48 8d 57 2c          	lea    0x2c(%rdi),%rdx
	sqe->personality = 0;
    ad06:	66 89 47 2a          	mov    %ax,0x2a(%rdi)
	sqe->file_index = 0;
    ad0a:	48 89 d0             	mov    %rdx,%rax
    ad0d:	48 c1 e8 03          	shr    $0x3,%rax
    ad11:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    ad18:	48 89 d0             	mov    %rdx,%rax
    ad1b:	83 e0 07             	and    $0x7,%eax
    ad1e:	83 c0 03             	add    $0x3,%eax
    ad21:	38 c8                	cmp    %cl,%al
    ad23:	7c 08                	jl     ad2d <_send_static_string_content+0x3cd>
    ad25:	84 c9                	test   %cl,%cl
    ad27:	0f 85 5e 01 00 00    	jne    ae8b <_send_static_string_content+0x52b>
	sqe->addr3 = 0;
    ad2d:	48 8d 47 30          	lea    0x30(%rdi),%rax
	sqe->file_index = 0;
    ad31:	c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%rdi)
	sqe->addr3 = 0;
    ad38:	48 89 c2             	mov    %rax,%rdx
    ad3b:	48 c1 ea 03          	shr    $0x3,%rdx
    ad3f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    ad46:	0f 85 94 01 00 00    	jne    aee0 <_send_static_string_content+0x580>
	sqe->__pad2[0] = 0;
    ad4c:	48 8d 47 38          	lea    0x38(%rdi),%rax
	sqe->addr3 = 0;
    ad50:	48 c7 47 30 00 00 00 00 	movq   $0x0,0x30(%rdi)
	sqe->__pad2[0] = 0;
    ad58:	48 89 c2             	mov    %rax,%rdx
    ad5b:	48 c1 ea 03          	shr    $0x3,%rdx
    ad5f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    ad66:	0f 85 7c 01 00 00    	jne    aee8 <_send_static_string_content+0x588>
	sqe->user_data = (unsigned long) data;
    ad6c:	48 8d 47 20          	lea    0x20(%rdi),%rax
	sqe->__pad2[0] = 0;
    ad70:	48 c7 47 38 00 00 00 00 	movq   $0x0,0x38(%rdi)
	sqe->user_data = (unsigned long) data;
    ad78:	48 89 c2             	mov    %rax,%rdx
    ad7b:	48 c1 ea 03          	shr    $0x3,%rdx
    ad7f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    ad86:	0f 85 4c 01 00 00    	jne    aed8 <_send_static_string_content+0x578>
    ad8c:	48 89 6f 20          	mov    %rbp,0x20(%rdi)
    io_uring_submit(ring);
    ad90:	48 89 df             	mov    %rbx,%rdi
}
    ad93:	5b                   	pop    %rbx
    ad94:	5d                   	pop    %rbp
    ad95:	41 5c                	pop    %r12
    ad97:	41 5d                	pop    %r13
    ad99:	41 5e                	pop    %r14
    io_uring_submit(ring);
    ad9b:	e9 c0 98 ff ff       	jmp    4660 <io_uring_submit@plt>
		head = io_uring_smp_load_acquire(sq->khead);
    ada0:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    ada7:	0f 85 4b 01 00 00    	jne    aef8 <_send_static_string_content+0x598>
    adad:	48 8b 3b             	mov    (%rbx),%rdi
    adb0:	48 89 fa             	mov    %rdi,%rdx
    adb3:	48 c1 ea 03          	shr    $0x3,%rdx
    adb7:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    adbe:	48 89 fa             	mov    %rdi,%rdx
    adc1:	83 e2 07             	and    $0x7,%edx
    adc4:	83 c2 03             	add    $0x3,%edx
    adc7:	40 38 f2             	cmp    %sil,%dl
    adca:	7c 05                	jl     add1 <_send_static_string_content+0x471>
    adcc:	40 84 f6             	test   %sil,%sil
    adcf:	75 20                	jne    adf1 <_send_static_string_content+0x491>
    add1:	8b 17                	mov    (%rdi),%edx
    add3:	e9 01 fd ff ff       	jmp    aad9 <_send_static_string_content+0x179>
	unsigned int head, next = sq->sqe_tail + 1;
    add8:	e8 73 97 ff ff       	call   4550 <__asan_report_load4@plt>
    req->iovec_count = 1;
    addd:	e8 de 98 ff ff       	call   46c0 <__asan_report_store4@plt>
    req->client_socket = client_socket;
    ade2:	e8 d9 98 ff ff       	call   46c0 <__asan_report_store4@plt>
	if (ring->flags & IORING_SETUP_SQE128)
    ade7:	e8 64 97 ff ff       	call   4550 <__asan_report_load4@plt>
		head = IO_URING_READ_ONCE(*sq->khead);
    adec:	e8 5f 97 ff ff       	call   4550 <__asan_report_load4@plt>
		head = io_uring_smp_load_acquire(sq->khead);
    adf1:	e8 5a 97 ff ff       	call   4550 <__asan_report_load4@plt>
    req->iov[0].iov_len = slen;
    adf6:	48 89 c7             	mov    %rax,%rdi
    adf9:	e8 d2 98 ff ff       	call   46d0 <__asan_report_store8@plt>
	if (next - head <= sq->ring_entries) {
    adfe:	e8 4d 97 ff ff       	call   4550 <__asan_report_load4@plt>
    req->iov[0].iov_base = zh_malloc(slen);
    ae03:	4c 89 f7             	mov    %r14,%rdi
    ae06:	e8 c5 98 ff ff       	call   46d0 <__asan_report_store8@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    ae0b:	48 8d 3d 0e bd 00 00 	lea    0xbd0e(%rip),%rdi        # 16b20 <stderr@GLIBC_2.2.5>
    ae12:	48 89 f8             	mov    %rdi,%rax
    ae15:	48 c1 e8 03          	shr    $0x3,%rax
    ae19:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ae20:	0f 85 da 00 00 00    	jne    af00 <_send_static_string_content+0x5a0>
    ae26:	48 8b 0d f3 bc 00 00 	mov    0xbcf3(%rip),%rcx        # 16b20 <stderr@GLIBC_2.2.5>
    ae2d:	ba 28 00 00 00       	mov    $0x28,%edx
    ae32:	be 01 00 00 00       	mov    $0x1,%esi
    ae37:	48 8d 3d 62 64 00 00 	lea    0x6462(%rip),%rdi        # 112a0 <_IO_stdin_used+0x2a0>
    ae3e:	e8 5d 96 ff ff       	call   44a0 <fwrite@plt>
        exit(1);
    ae43:	e8 c8 97 ff ff       	call   4610 <__asan_handle_no_return@plt>
    ae48:	bf 01 00 00 00       	mov    $0x1,%edi
    ae4d:	e8 be 96 ff ff       	call   4510 <exit@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    ae52:	48 8d 3d c7 bc 00 00 	lea    0xbcc7(%rip),%rdi        # 16b20 <stderr@GLIBC_2.2.5>
    ae59:	48 89 f8             	mov    %rdi,%rax
    ae5c:	48 c1 e8 03          	shr    $0x3,%rax
    ae60:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ae67:	74 bd                	je     ae26 <_send_static_string_content+0x4c6>
    ae69:	e8 72 96 ff ff       	call   44e0 <__asan_report_load8@plt>
    req->event_type = EVENT_TYPE_WRITE;
    ae6e:	48 89 ef             	mov    %rbp,%rdi
    ae71:	e8 4a 98 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->opcode = (__u8) op;
    ae76:	e8 55 99 ff ff       	call   47d0 <__asan_report_store1@plt>
	sqe->flags = 0;
    ae7b:	48 89 c7             	mov    %rax,%rdi
    ae7e:	e8 4d 99 ff ff       	call   47d0 <__asan_report_store1@plt>
	sqe->personality = 0;
    ae83:	48 89 d7             	mov    %rdx,%rdi
    ae86:	e8 75 96 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->file_index = 0;
    ae8b:	48 89 d7             	mov    %rdx,%rdi
    ae8e:	e8 2d 98 ff ff       	call   46c0 <__asan_report_store4@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    ae93:	e8 48 96 ff ff       	call   44e0 <__asan_report_load8@plt>
    ae98:	4c 89 c7             	mov    %r8,%rdi
    ae9b:	e8 b0 96 ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->rw_flags = 0;
    aea0:	48 89 d7             	mov    %rdx,%rdi
    aea3:	e8 18 98 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->buf_index = 0;
    aea8:	48 89 d7             	mov    %rdx,%rdi
    aeab:	e8 50 96 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->ioprio = 0;
    aeb0:	48 89 d7             	mov    %rdx,%rdi
    aeb3:	e8 48 96 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->fd = fd;
    aeb8:	48 89 d7             	mov    %rdx,%rdi
    aebb:	e8 00 98 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->off = offset;
    aec0:	48 89 c7             	mov    %rax,%rdi
    aec3:	e8 08 98 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->addr = (unsigned long) addr;
    aec8:	48 89 c7             	mov    %rax,%rdi
    aecb:	e8 00 98 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->len = len;
    aed0:	48 89 d7             	mov    %rdx,%rdi
    aed3:	e8 e8 97 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->user_data = (unsigned long) data;
    aed8:	48 89 c7             	mov    %rax,%rdi
    aedb:	e8 f0 97 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->addr3 = 0;
    aee0:	48 89 c7             	mov    %rax,%rdi
    aee3:	e8 e8 97 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->__pad2[0] = 0;
    aee8:	48 89 c7             	mov    %rax,%rdi
    aeeb:	e8 e0 97 ff ff       	call   46d0 <__asan_report_store8@plt>
		head = IO_URING_READ_ONCE(*sq->khead);
    aef0:	48 89 df             	mov    %rbx,%rdi
    aef3:	e8 e8 95 ff ff       	call   44e0 <__asan_report_load8@plt>
		head = io_uring_smp_load_acquire(sq->khead);
    aef8:	48 89 df             	mov    %rbx,%rdi
    aefb:	e8 e0 95 ff ff       	call   44e0 <__asan_report_load8@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    af00:	e8 db 95 ff ff       	call   44e0 <__asan_report_load8@plt>
    af05:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

000000000000af10 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    af10:	f3 0f 1e fa          	endbr64
    af14:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    af17:	89 fe                	mov    %edi,%esi
    af19:	48 8b 3d 40 a1 00 00 	mov    0xa140(%rip),%rdi        # 15060 <unimplemented_content>
    af20:	e9 3b fa ff ff       	jmp    a960 <_send_static_string_content>
    af25:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

000000000000af30 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    af30:	f3 0f 1e fa          	endbr64
    af34:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    af37:	89 fe                	mov    %edi,%esi
    af39:	48 8b 3d e0 a0 00 00 	mov    0xa0e0(%rip),%rdi        # 15020 <http_404_content>
    af40:	e9 1b fa ff ff       	jmp    a960 <_send_static_string_content>
    af45:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

000000000000af50 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    af50:	f3 0f 1e fa          	endbr64
    af54:	41 57                	push   %r15
    af56:	41 56                	push   %r14
    af58:	41 55                	push   %r13
    af5a:	41 54                	push   %r12
    af5c:	49 89 fc             	mov    %rdi,%r12
    af5f:	55                   	push   %rbp
    af60:	53                   	push   %rbx
    af61:	48 81 ec c8 05 00 00 	sub    $0x5c8,%rsp
    af68:	8b 05 92 bb 00 00    	mov    0xbb92(%rip),%eax        # 16b00 <__asan_option_detect_stack_use_after_return@@Base>
    af6e:	48 8d 5c 24 20       	lea    0x20(%rsp),%rbx
    af73:	89 74 24 10          	mov    %esi,0x10(%rsp)
    af77:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    af7c:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    af81:	85 c0                	test   %eax,%eax
    af83:	0f 85 66 03 00 00    	jne    b2ef <handle_get_method+0x39f>
    af89:	48 8d 05 68 7f 00 00 	lea    0x7f68(%rip),%rax        # 12ef8 <_IO_stdin_used+0x1ef8>
    af90:	49 89 df             	mov    %rbx,%r15
    af93:	48 c7 03 b3 8a b5 41 	movq   $0x41b58ab3,(%rbx)
    if (path[strlen(path) - 1] == '/') {
    af9a:	4c 89 e7             	mov    %r12,%rdi
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    af9d:	48 89 43 08          	mov    %rax,0x8(%rbx)
    afa1:	49 c1 ef 03          	shr    $0x3,%r15
    afa5:	48 8d 05 a4 ff ff ff 	lea    -0x5c(%rip),%rax        # af50 <handle_get_method>
    afac:	48 8d ab a0 05 00 00 	lea    0x5a0(%rbx),%rbp
    afb3:	48 89 43 10          	mov    %rax,0x10(%rbx)
    afb7:	41 c7 87 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%r15)
    afc2:	41 c7 87 04 80 ff 7f f1 f1 00 00 	movl   $0xf1f1,0x7fff8004(%r15)
    afcd:	41 c7 87 18 80 ff 7f f2 f2 f2 f2 	movl   $0xf2f2f2f2,0x7fff8018(%r15)
    afd8:	41 c7 87 1c 80 ff 7f f2 f2 f2 f2 	movl   $0xf2f2f2f2,0x7fff801c(%r15)
    afe3:	41 c7 87 a0 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff80a0(%r15)
    afee:	41 c7 87 a4 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff80a4(%r15)
    aff9:	41 c7 87 a8 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff80a8(%r15)
    b004:	41 c7 87 ac 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff80ac(%r15)
    b00f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    b018:	48 89 84 24 b8 05 00 00 	mov    %rax,0x5b8(%rsp)
    b020:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    b022:	e8 b9 95 ff ff       	call   45e0 <strlen@plt>
    b027:	49 8d 7c 04 ff       	lea    -0x1(%r12,%rax,1),%rdi
    b02c:	49 89 c6             	mov    %rax,%r14
    b02f:	48 89 f8             	mov    %rdi,%rax
    b032:	48 89 fa             	mov    %rdi,%rdx
    b035:	48 c1 e8 03          	shr    $0x3,%rax
    b039:	83 e2 07             	and    $0x7,%edx
    b03c:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    b043:	38 d0                	cmp    %dl,%al
    b045:	7f 08                	jg     b04f <handle_get_method+0xff>
    b047:	84 c0                	test   %al,%al
    b049:	0f 85 8c 02 00 00    	jne    b2db <handle_get_method+0x38b>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    b04f:	4c 8d ad 60 fb ff ff 	lea    -0x4a0(%rbp),%r13
    b056:	80 3f 2f             	cmpb   $0x2f,(%rdi)
    b059:	ba 06 00 00 00       	mov    $0x6,%edx
    b05e:	48 8d 35 7b 68 00 00 	lea    0x687b(%rip),%rsi        # 118e0 <_IO_stdin_used+0x8e0>
    b065:	4c 89 ef             	mov    %r13,%rdi
    b068:	0f 84 f2 00 00 00    	je     b160 <handle_get_method+0x210>
    b06e:	e8 4d 94 ff ff       	call   44c0 <memcpy@plt>


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    b073:	49 8d 56 01          	lea    0x1(%r14),%rdx
    b077:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    b07c:	4c 89 e6             	mov    %r12,%rsi
    b07f:	48 8d bd 66 fb ff ff 	lea    -0x49a(%rbp),%rdi
    b086:	e8 25 95 ff ff       	call   45b0 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    b08b:	48 8d b5 90 fa ff ff 	lea    -0x570(%rbp),%rsi
    b092:	4c 89 ef             	mov    %r13,%rdi
    b095:	e8 56 95 ff ff       	call   45f0 <stat@plt>
    b09a:	83 f8 ff             	cmp    $0xffffffff,%eax
    b09d:	0f 84 05 02 00 00    	je     b2a8 <handle_get_method+0x358>
        if (S_ISREG(path_stat.st_mode)) {
    b0a3:	48 8d bd a8 fa ff ff 	lea    -0x558(%rbp),%rdi
    b0aa:	48 89 f8             	mov    %rdi,%rax
    b0ad:	48 c1 e8 03          	shr    $0x3,%rax
    b0b1:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    b0b8:	84 c0                	test   %al,%al
    b0ba:	74 08                	je     b0c4 <handle_get_method+0x174>
    b0bc:	3c 03                	cmp    $0x3,%al
    b0be:	0f 8e 1c 02 00 00    	jle    b2e0 <handle_get_method+0x390>
    b0c4:	8b 85 a8 fa ff ff    	mov    -0x558(%rbp),%eax
    b0ca:	25 00 f0 00 00       	and    $0xf000,%eax
    b0cf:	3d 00 80 00 00       	cmp    $0x8000,%eax
    b0d4:	0f 84 c6 00 00 00    	je     b1a0 <handle_get_method+0x250>
    _send_static_string_content(http_404_content, client_socket, ring);
    b0da:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    b0df:	8b 74 24 10          	mov    0x10(%rsp),%esi
    b0e3:	48 8b 3d 36 9f 00 00 	mov    0x9f36(%rip),%rdi        # 15020 <http_404_content>
    b0ea:	e8 71 f8 ff ff       	call   a960 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    b0ef:	4c 89 ea             	mov    %r13,%rdx
    b0f2:	bf 01 00 00 00       	mov    $0x1,%edi
    b0f7:	31 c0                	xor    %eax,%eax
    b0f9:	48 8d 35 e0 68 00 00 	lea    0x68e0(%rip),%rsi        # 119e0 <_IO_stdin_used+0x9e0>
    b100:	e8 1b 94 ff ff       	call   4520 <__printf_chk@plt>
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    b105:	48 39 5c 24 08       	cmp    %rbx,0x8(%rsp)
    b10a:	0f 85 f5 01 00 00    	jne    b305 <handle_get_method+0x3b5>
    b110:	49 c7 87 00 80 ff 7f 00 00 00 00 	movq   $0x0,0x7fff8000(%r15)
    b11b:	66 0f ef c0          	pxor   %xmm0,%xmm0
    b11f:	49 c7 87 18 80 ff 7f 00 00 00 00 	movq   $0x0,0x7fff8018(%r15)
    b12a:	41 0f 11 87 a0 80 ff 7f 	movups %xmm0,0x7fff80a0(%r15)
}
    b132:	48 8b 84 24 b8 05 00 00 	mov    0x5b8(%rsp),%rax
    b13a:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    b143:	0f 85 da 01 00 00    	jne    b323 <handle_get_method+0x3d3>
    b149:	48 81 c4 c8 05 00 00 	add    $0x5c8,%rsp
    b150:	5b                   	pop    %rbx
    b151:	5d                   	pop    %rbp
    b152:	41 5c                	pop    %r12
    b154:	41 5d                	pop    %r13
    b156:	41 5e                	pop    %r14
    b158:	41 5f                	pop    %r15
    b15a:	c3                   	ret
    b15b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    b160:	e8 5b 93 ff ff       	call   44c0 <memcpy@plt>
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    b165:	4c 89 f2             	mov    %r14,%rdx
    b168:	4c 89 e6             	mov    %r12,%rsi
    b16b:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    b170:	48 8d bd 66 fb ff ff 	lea    -0x49a(%rbp),%rdi
    b177:	e8 34 94 ff ff       	call   45b0 <__memcpy_chk@plt>
    b17c:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    b181:	4b 8d 7c 2e 06       	lea    0x6(%r14,%r13,1),%rdi
    b186:	ba 0b 00 00 00       	mov    $0xb,%edx
    b18b:	4c 29 f1             	sub    %r14,%rcx
    b18e:	48 8d 35 8b 67 00 00 	lea    0x678b(%rip),%rsi        # 11920 <_IO_stdin_used+0x920>
    b195:	e8 16 94 ff ff       	call   45b0 <__memcpy_chk@plt>
    b19a:	e9 ec fe ff ff       	jmp    b08b <handle_get_method+0x13b>
    b19f:	90                   	nop
    void *buf = malloc(size);
    b1a0:	bf 70 00 00 00       	mov    $0x70,%edi
    b1a5:	e8 e6 93 ff ff       	call   4590 <malloc@plt>
    b1aa:	49 89 c4             	mov    %rax,%r12
    if (!buf) {
    b1ad:	48 85 c0             	test   %rax,%rax
    b1b0:	0f 84 84 01 00 00    	je     b33a <handle_get_method+0x3ea>
            req->iovec_count = 6;
    b1b6:	48 8d 78 04          	lea    0x4(%rax),%rdi
    b1ba:	48 89 f8             	mov    %rdi,%rax
    b1bd:	48 c1 e8 03          	shr    $0x3,%rax
    b1c1:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    b1c8:	48 89 f8             	mov    %rdi,%rax
    b1cb:	83 e0 07             	and    $0x7,%eax
    b1ce:	83 c0 03             	add    $0x3,%eax
    b1d1:	38 d0                	cmp    %dl,%al
    b1d3:	7c 08                	jl     b1dd <handle_get_method+0x28d>
    b1d5:	84 d2                	test   %dl,%dl
    b1d7:	0f 85 08 01 00 00    	jne    b2e5 <handle_get_method+0x395>
    b1dd:	41 c7 44 24 04 06 00 00 00 	movl   $0x6,0x4(%r12)
            req->client_socket = client_socket;
    b1e6:	49 8d 7c 24 08       	lea    0x8(%r12),%rdi
    b1eb:	48 89 f8             	mov    %rdi,%rax
    b1ee:	48 c1 e8 03          	shr    $0x3,%rax
    b1f2:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    b1f9:	84 c0                	test   %al,%al
    b1fb:	74 08                	je     b205 <handle_get_method+0x2b5>
    b1fd:	3c 03                	cmp    $0x3,%al
    b1ff:	0f 8e e5 00 00 00    	jle    b2ea <handle_get_method+0x39a>
    b205:	8b 44 24 10          	mov    0x10(%rsp),%eax
            send_headers(final_path, path_stat.st_size, req->iov);
    b209:	49 8d 54 24 10       	lea    0x10(%r12),%rdx
            req->client_socket = client_socket;
    b20e:	41 89 44 24 08       	mov    %eax,0x8(%r12)
            send_headers(final_path, path_stat.st_size, req->iov);
    b213:	48 8d 85 c0 fa ff ff 	lea    -0x540(%rbp),%rax
    b21a:	49 89 c6             	mov    %rax,%r14
    b21d:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    b222:	49 c1 ee 03          	shr    $0x3,%r14
    b226:	41 80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r14)
    b22e:	0f 85 f4 00 00 00    	jne    b328 <handle_get_method+0x3d8>
    b234:	48 8b b5 c0 fa ff ff 	mov    -0x540(%rbp),%rsi
    b23b:	4c 89 ef             	mov    %r13,%rdi
    b23e:	e8 8d e4 ff ff       	call   96d0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    b243:	41 80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r14)
    b24b:	49 8d 54 24 60       	lea    0x60(%r12),%rdx
    b250:	0f 85 da 00 00 00    	jne    b330 <handle_get_method+0x3e0>
    b256:	48 8b b5 c0 fa ff ff 	mov    -0x540(%rbp),%rsi
    b25d:	4c 89 ef             	mov    %r13,%rdi
    b260:	e8 2b ec ff ff       	call   9e90 <copy_file_contents>
            printf("200 %s %ld bytes\n", final_path, path_stat.st_size);
    b265:	41 80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r14)
    b26d:	0f 85 0a 01 00 00    	jne    b37d <handle_get_method+0x42d>
    b273:	48 8b 8d c0 fa ff ff 	mov    -0x540(%rbp),%rcx
    b27a:	4c 89 ea             	mov    %r13,%rdx
    b27d:	bf 01 00 00 00       	mov    $0x1,%edi
    b282:	31 c0                	xor    %eax,%eax
    b284:	48 8d 35 15 67 00 00 	lea    0x6715(%rip),%rsi        # 119a0 <_IO_stdin_used+0x9a0>
    b28b:	e8 90 92 ff ff       	call   4520 <__printf_chk@plt>
            add_write_request(req, ring);
    b290:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    b295:	4c 89 e7             	mov    %r12,%rdi
    b298:	e8 23 ed ff ff       	call   9fc0 <add_write_request>
    b29d:	e9 63 fe ff ff       	jmp    b105 <handle_get_method+0x1b5>
    b2a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    b2a8:	4c 89 ea             	mov    %r13,%rdx
    b2ab:	4c 89 e1             	mov    %r12,%rcx
    b2ae:	48 8d 35 ab 66 00 00 	lea    0x66ab(%rip),%rsi        # 11960 <_IO_stdin_used+0x960>
    b2b5:	31 c0                	xor    %eax,%eax
    b2b7:	bf 01 00 00 00       	mov    $0x1,%edi
    b2bc:	e8 5f 92 ff ff       	call   4520 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    b2c1:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    b2c6:	8b 74 24 10          	mov    0x10(%rsp),%esi
    b2ca:	48 8b 3d 4f 9d 00 00 	mov    0x9d4f(%rip),%rdi        # 15020 <http_404_content>
    b2d1:	e8 8a f6 ff ff       	call   a960 <_send_static_string_content>
}
    b2d6:	e9 2a fe ff ff       	jmp    b105 <handle_get_method+0x1b5>
    if (path[strlen(path) - 1] == '/') {
    b2db:	e8 b0 94 ff ff       	call   4790 <__asan_report_load1@plt>
        if (S_ISREG(path_stat.st_mode)) {
    b2e0:	e8 6b 92 ff ff       	call   4550 <__asan_report_load4@plt>
            req->iovec_count = 6;
    b2e5:	e8 d6 93 ff ff       	call   46c0 <__asan_report_store4@plt>
            req->client_socket = client_socket;
    b2ea:	e8 d1 93 ff ff       	call   46c0 <__asan_report_store4@plt>
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    b2ef:	bf 80 05 00 00       	mov    $0x580,%edi
    b2f4:	e8 77 94 ff ff       	call   4770 <__asan_stack_malloc_5@plt>
    b2f9:	48 85 c0             	test   %rax,%rax
    b2fc:	48 0f 45 d8          	cmovne %rax,%rbx
    b300:	e9 84 fc ff ff       	jmp    af89 <handle_get_method+0x39>
    b305:	48 c7 03 0e 36 e0 45 	movq   $0x45e0360e,(%rbx)
    b30c:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    b311:	be 80 05 00 00       	mov    $0x580,%esi
    b316:	48 89 df             	mov    %rbx,%rdi
    b319:	e8 62 93 ff ff       	call   4680 <__asan_stack_free_5@plt>
    b31e:	e9 0f fe ff ff       	jmp    b132 <handle_get_method+0x1e2>
}
    b323:	e8 88 93 ff ff       	call   46b0 <__stack_chk_fail@plt>
            send_headers(final_path, path_stat.st_size, req->iov);
    b328:	48 89 c7             	mov    %rax,%rdi
    b32b:	e8 b0 91 ff ff       	call   44e0 <__asan_report_load8@plt>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    b330:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    b335:	e8 a6 91 ff ff       	call   44e0 <__asan_report_load8@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    b33a:	48 8d 3d df b7 00 00 	lea    0xb7df(%rip),%rdi        # 16b20 <stderr@GLIBC_2.2.5>
    b341:	48 89 f8             	mov    %rdi,%rax
    b344:	48 c1 e8 03          	shr    $0x3,%rax
    b348:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    b34f:	75 36                	jne    b387 <handle_get_method+0x437>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    b351:	48 8b 0d c8 b7 00 00 	mov    0xb7c8(%rip),%rcx        # 16b20 <stderr@GLIBC_2.2.5>
    b358:	ba 28 00 00 00       	mov    $0x28,%edx
    b35d:	be 01 00 00 00       	mov    $0x1,%esi
    b362:	48 8d 3d 37 5f 00 00 	lea    0x5f37(%rip),%rdi        # 112a0 <_IO_stdin_used+0x2a0>
    b369:	e8 32 91 ff ff       	call   44a0 <fwrite@plt>
        exit(1);
    b36e:	e8 9d 92 ff ff       	call   4610 <__asan_handle_no_return@plt>
    b373:	bf 01 00 00 00       	mov    $0x1,%edi
    b378:	e8 93 91 ff ff       	call   4510 <exit@plt>
            printf("200 %s %ld bytes\n", final_path, path_stat.st_size);
    b37d:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    b382:	e8 59 91 ff ff       	call   44e0 <__asan_report_load8@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    b387:	e8 54 91 ff ff       	call   44e0 <__asan_report_load8@plt>
    b38c:	0f 1f 40 00          	nopl   0x0(%rax)

000000000000b390 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    b390:	f3 0f 1e fa          	endbr64
    b394:	41 57                	push   %r15
    b396:	41 56                	push   %r14
    b398:	41 55                	push   %r13
    b39a:	41 54                	push   %r12
    b39c:	49 89 fc             	mov    %rdi,%r12
    b39f:	55                   	push   %rbp
    b3a0:	53                   	push   %rbx
    b3a1:	48 83 ec 78          	sub    $0x78,%rsp
    b3a5:	8b 05 55 b7 00 00    	mov    0xb755(%rip),%eax        # 16b00 <__asan_option_detect_stack_use_after_return@@Base>
    b3ab:	48 8d 6c 24 10       	lea    0x10(%rsp),%rbp
    b3b0:	89 74 24 08          	mov    %esi,0x8(%rsp)
    b3b4:	48 89 14 24          	mov    %rdx,(%rsp)
    b3b8:	49 89 ef             	mov    %rbp,%r15
    b3bb:	85 c0                	test   %eax,%eax
    b3bd:	0f 85 d5 01 00 00    	jne    b598 <handle_http_method+0x208>
    b3c3:	48 8d 05 96 7c 00 00 	lea    0x7c96(%rip),%rax        # 13060 <_IO_stdin_used+0x2060>
    b3ca:	48 89 eb             	mov    %rbp,%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    b3cd:	48 8d 55 20          	lea    0x20(%rbp),%rdx
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    b3d1:	48 c7 45 00 b3 8a b5 41 	movq   $0x41b58ab3,0x0(%rbp)
    b3d9:	48 89 45 08          	mov    %rax,0x8(%rbp)
    b3dd:	48 c1 eb 03          	shr    $0x3,%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    b3e1:	4c 89 e7             	mov    %r12,%rdi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    b3e4:	4c 8d 6d 60          	lea    0x60(%rbp),%r13
    b3e8:	48 8d 05 a1 ff ff ff 	lea    -0x5f(%rip),%rax        # b390 <handle_http_method>
    method = strtok_r(method_buffer, " ", &saveptr);
    b3ef:	4c 8d 35 2a 66 00 00 	lea    0x662a(%rip),%r14        # 11a20 <_IO_stdin_used+0xa20>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    b3f6:	48 89 45 10          	mov    %rax,0x10(%rbp)
    method = strtok_r(method_buffer, " ", &saveptr);
    b3fa:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    b3fd:	c7 83 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%rbx)
    b407:	c7 83 04 80 ff 7f 00 f3 f3 f3 	movl   $0xf3f3f300,0x7fff8004(%rbx)
    b411:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    b41a:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    b41f:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    b421:	e8 1a 92 ff ff       	call   4640 <strtok_r@plt>
    b426:	49 89 c4             	mov    %rax,%r12
    for (; *str; ++str)
    b429:	48 c1 e8 03          	shr    $0x3,%rax
    b42d:	4c 89 e2             	mov    %r12,%rdx
    b430:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    b437:	83 e2 07             	and    $0x7,%edx
    b43a:	38 d0                	cmp    %dl,%al
    b43c:	7f 08                	jg     b446 <handle_http_method+0xb6>
    b43e:	84 c0                	test   %al,%al
    b440:	0f 85 30 01 00 00    	jne    b576 <handle_http_method+0x1e6>
    b446:	41 0f b6 14 24       	movzbl (%r12),%edx
    b44b:	84 d2                	test   %dl,%dl
    b44d:	88 54 24 0f          	mov    %dl,0xf(%rsp)
    b451:	0f 84 aa 00 00 00    	je     b501 <handle_http_method+0x171>
        *str = (char)tolower(*str);
    b457:	e8 94 92 ff ff       	call   46f0 <__ctype_tolower_loc@plt>
    b45c:	48 0f be 54 24 0f    	movsbq 0xf(%rsp),%rdx
    b462:	4c 89 e7             	mov    %r12,%rdi
    b465:	49 89 c1             	mov    %rax,%r9
    b468:	48 89 c6             	mov    %rax,%rsi
    b46b:	49 c1 e9 03          	shr    $0x3,%r9
    b46f:	90                   	nop
    b470:	41 80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r9)
    b478:	0f 85 12 01 00 00    	jne    b590 <handle_http_method+0x200>
    b47e:	48 8b 06             	mov    (%rsi),%rax
    b481:	48 8d 04 90          	lea    (%rax,%rdx,4),%rax
    b485:	48 89 c2             	mov    %rax,%rdx
    b488:	48 c1 ea 03          	shr    $0x3,%rdx
    b48c:	44 0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%r10d
    b494:	48 89 c2             	mov    %rax,%rdx
    b497:	83 e2 07             	and    $0x7,%edx
    b49a:	83 c2 03             	add    $0x3,%edx
    b49d:	44 38 d2             	cmp    %r10b,%dl
    b4a0:	7c 09                	jl     b4ab <handle_http_method+0x11b>
    b4a2:	45 84 d2             	test   %r10b,%r10b
    b4a5:	0f 85 dd 00 00 00    	jne    b588 <handle_http_method+0x1f8>
    b4ab:	8b 10                	mov    (%rax),%edx
    b4ad:	48 89 f8             	mov    %rdi,%rax
    b4b0:	49 89 fa             	mov    %rdi,%r10
    b4b3:	48 c1 e8 03          	shr    $0x3,%rax
    b4b7:	41 83 e2 07          	and    $0x7,%r10d
    b4bb:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    b4c2:	44 38 d0             	cmp    %r10b,%al
    b4c5:	7f 08                	jg     b4cf <handle_http_method+0x13f>
    b4c7:	84 c0                	test   %al,%al
    b4c9:	0f 85 b4 00 00 00    	jne    b583 <handle_http_method+0x1f3>
    b4cf:	88 17                	mov    %dl,(%rdi)
    for (; *str; ++str)
    b4d1:	48 83 c7 01          	add    $0x1,%rdi
    b4d5:	48 89 f8             	mov    %rdi,%rax
    b4d8:	48 89 fa             	mov    %rdi,%rdx
    b4db:	48 c1 e8 03          	shr    $0x3,%rax
    b4df:	83 e2 07             	and    $0x7,%edx
    b4e2:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    b4e9:	38 d0                	cmp    %dl,%al
    b4eb:	7f 08                	jg     b4f5 <handle_http_method+0x165>
    b4ed:	84 c0                	test   %al,%al
    b4ef:	0f 85 89 00 00 00    	jne    b57e <handle_http_method+0x1ee>
    b4f5:	48 0f be 17          	movsbq (%rdi),%rdx
    b4f9:	84 d2                	test   %dl,%dl
    b4fb:	0f 85 6f ff ff ff    	jne    b470 <handle_http_method+0xe0>
    path = strtok_r(NULL, " ", &saveptr);
    b501:	49 8d 55 c0          	lea    -0x40(%r13),%rdx
    b505:	4c 89 f6             	mov    %r14,%rsi
    b508:	31 ff                	xor    %edi,%edi
    b50a:	e8 31 91 ff ff       	call   4640 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    b50f:	48 8d 35 4a 65 00 00 	lea    0x654a(%rip),%rsi        # 11a60 <_IO_stdin_used+0xa60>
    b516:	4c 89 e7             	mov    %r12,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    b519:	49 89 c5             	mov    %rax,%r13
    if (strcmp(method, "get") == 0) {
    b51c:	e8 0f 92 ff ff       	call   4730 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    b521:	48 8b 14 24          	mov    (%rsp),%rdx
    b525:	8b 74 24 08          	mov    0x8(%rsp),%esi
    if (strcmp(method, "get") == 0) {
    b529:	85 c0                	test   %eax,%eax
    b52b:	75 3b                	jne    b568 <handle_http_method+0x1d8>
        handle_get_method(path, client_socket, ring);
    b52d:	4c 89 ef             	mov    %r13,%rdi
    b530:	e8 1b fa ff ff       	call   af50 <handle_get_method>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    b535:	49 39 ef             	cmp    %rbp,%r15
    b538:	75 74                	jne    b5ae <handle_http_method+0x21e>
    b53a:	48 c7 83 00 80 ff 7f 00 00 00 00 	movq   $0x0,0x7fff8000(%rbx)
}
    b545:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    b54a:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    b553:	75 7e                	jne    b5d3 <handle_http_method+0x243>
    b555:	48 83 c4 78          	add    $0x78,%rsp
    b559:	5b                   	pop    %rbx
    b55a:	5d                   	pop    %rbp
    b55b:	41 5c                	pop    %r12
    b55d:	41 5d                	pop    %r13
    b55f:	41 5e                	pop    %r14
    b561:	41 5f                	pop    %r15
    b563:	c3                   	ret
    b564:	0f 1f 40 00          	nopl   0x0(%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    b568:	48 8b 3d f1 9a 00 00 	mov    0x9af1(%rip),%rdi        # 15060 <unimplemented_content>
    b56f:	e8 ec f3 ff ff       	call   a960 <_send_static_string_content>
}
    b574:	eb bf                	jmp    b535 <handle_http_method+0x1a5>
    for (; *str; ++str)
    b576:	4c 89 e7             	mov    %r12,%rdi
    b579:	e8 12 92 ff ff       	call   4790 <__asan_report_load1@plt>
    b57e:	e8 0d 92 ff ff       	call   4790 <__asan_report_load1@plt>
        *str = (char)tolower(*str);
    b583:	e8 48 92 ff ff       	call   47d0 <__asan_report_store1@plt>
    b588:	48 89 c7             	mov    %rax,%rdi
    b58b:	e8 c0 8f ff ff       	call   4550 <__asan_report_load4@plt>
    b590:	48 89 f7             	mov    %rsi,%rdi
    b593:	e8 48 8f ff ff       	call   44e0 <__asan_report_load8@plt>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    b598:	bf 40 00 00 00       	mov    $0x40,%edi
    b59d:	e8 0e 92 ff ff       	call   47b0 <__asan_stack_malloc_0@plt>
    b5a2:	48 85 c0             	test   %rax,%rax
    b5a5:	48 0f 45 e8          	cmovne %rax,%rbp
    b5a9:	e9 15 fe ff ff       	jmp    b3c3 <handle_http_method+0x33>
    b5ae:	48 b8 f5 f5 f5 f5 f5 f5 f5 f5 	movabs $0xf5f5f5f5f5f5f5f5,%rax
    b5b8:	48 c7 45 00 0e 36 e0 45 	movq   $0x45e0360e,0x0(%rbp)
    b5c0:	48 89 83 00 80 ff 7f 	mov    %rax,0x7fff8000(%rbx)
    b5c7:	48 8b 45 38          	mov    0x38(%rbp),%rax
    b5cb:	c6 00 00             	movb   $0x0,(%rax)
    b5ce:	e9 72 ff ff ff       	jmp    b545 <handle_http_method+0x1b5>
}
    b5d3:	e8 d8 90 ff ff       	call   46b0 <__stack_chk_fail@plt>
    b5d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

000000000000b5e0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    b5e0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    b5e4:	85 d2                	test   %edx,%edx
    b5e6:	0f 8e 9e 00 00 00    	jle    b68a <get_line+0xaa>
    b5ec:	48 63 d2             	movslq %edx,%rdx
int get_line(const char *src, char *dest, int dest_sz) {
    b5ef:	48 83 ec 08          	sub    $0x8,%rsp
    b5f3:	4c 8d 04 17          	lea    (%rdi,%rdx,1),%r8
    b5f7:	eb 13                	jmp    b60c <get_line+0x2c>
    b5f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int i = 0; i < dest_sz; i++) {
    b600:	48 89 d7             	mov    %rdx,%rdi
    b603:	48 83 c6 01          	add    $0x1,%rsi
    b607:	4c 39 c2             	cmp    %r8,%rdx
    b60a:	74 74                	je     b680 <get_line+0xa0>
        dest[i] = src[i];
    b60c:	48 89 f8             	mov    %rdi,%rax
    b60f:	48 89 fa             	mov    %rdi,%rdx
    b612:	48 c1 e8 03          	shr    $0x3,%rax
    b616:	83 e2 07             	and    $0x7,%edx
    b619:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    b620:	38 d0                	cmp    %dl,%al
    b622:	7f 04                	jg     b628 <get_line+0x48>
    b624:	84 c0                	test   %al,%al
    b626:	75 68                	jne    b690 <get_line+0xb0>
    b628:	48 89 f2             	mov    %rsi,%rdx
    b62b:	48 89 f1             	mov    %rsi,%rcx
    b62e:	0f b6 07             	movzbl (%rdi),%eax
    b631:	48 c1 ea 03          	shr    $0x3,%rdx
    b635:	83 e1 07             	and    $0x7,%ecx
    b638:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    b63f:	38 ca                	cmp    %cl,%dl
    b641:	7f 04                	jg     b647 <get_line+0x67>
    b643:	84 d2                	test   %dl,%dl
    b645:	75 4e                	jne    b695 <get_line+0xb5>
    b647:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    b649:	48 8d 57 01          	lea    0x1(%rdi),%rdx
    b64d:	3c 0d                	cmp    $0xd,%al
    b64f:	75 af                	jne    b600 <get_line+0x20>
    b651:	48 89 d0             	mov    %rdx,%rax
    b654:	48 89 d1             	mov    %rdx,%rcx
    b657:	48 c1 e8 03          	shr    $0x3,%rax
    b65b:	83 e1 07             	and    $0x7,%ecx
    b65e:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    b665:	38 c8                	cmp    %cl,%al
    b667:	7f 04                	jg     b66d <get_line+0x8d>
    b669:	84 c0                	test   %al,%al
    b66b:	75 30                	jne    b69d <get_line+0xbd>
    b66d:	80 7f 01 0a          	cmpb   $0xa,0x1(%rdi)
    b671:	75 8d                	jne    b600 <get_line+0x20>
            dest[i] = '\0';
    b673:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    b676:	31 c0                	xor    %eax,%eax
}
    b678:	48 83 c4 08          	add    $0x8,%rsp
    b67c:	c3                   	ret
    b67d:	0f 1f 00             	nopl   (%rax)
    return 1;
    b680:	b8 01 00 00 00       	mov    $0x1,%eax
}
    b685:	48 83 c4 08          	add    $0x8,%rsp
    b689:	c3                   	ret
    return 1;
    b68a:	b8 01 00 00 00       	mov    $0x1,%eax
}
    b68f:	c3                   	ret
        dest[i] = src[i];
    b690:	e8 fb 90 ff ff       	call   4790 <__asan_report_load1@plt>
    b695:	48 89 f7             	mov    %rsi,%rdi
    b698:	e8 33 91 ff ff       	call   47d0 <__asan_report_store1@plt>
        if (src[i] == '\r' && src[i+1] == '\n') {
    b69d:	48 89 d7             	mov    %rdx,%rdi
    b6a0:	e8 eb 90 ff ff       	call   4790 <__asan_report_load1@plt>
    b6a5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

000000000000b6b0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    b6b0:	f3 0f 1e fa          	endbr64
    b6b4:	41 56                	push   %r14
    b6b6:	49 89 f6             	mov    %rsi,%r14
    b6b9:	41 55                	push   %r13
    b6bb:	49 89 fd             	mov    %rdi,%r13
    b6be:	41 54                	push   %r12
    b6c0:	55                   	push   %rbp
    b6c1:	53                   	push   %rbx
    b6c2:	48 81 ec c0 04 00 00 	sub    $0x4c0,%rsp
    b6c9:	8b 05 31 b4 00 00    	mov    0xb431(%rip),%eax        # 16b00 <__asan_option_detect_stack_use_after_return@@Base>
    b6cf:	48 89 e3             	mov    %rsp,%rbx
    b6d2:	49 89 dc             	mov    %rbx,%r12
    b6d5:	85 c0                	test   %eax,%eax
    b6d7:	0f 85 12 02 00 00    	jne    b8ef <handle_client_request+0x23f>
    b6dd:	48 8d 05 92 79 00 00 	lea    0x7992(%rip),%rax        # 13076 <_IO_stdin_used+0x2076>
    b6e4:	48 89 dd             	mov    %rbx,%rbp
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
    b6e7:	49 8d 7d 10          	lea    0x10(%r13),%rdi
int handle_client_request(struct Request *req, struct io_uring *ring) {
    b6eb:	48 c7 03 b3 8a b5 41 	movq   $0x41b58ab3,(%rbx)
    b6f2:	48 89 43 08          	mov    %rax,0x8(%rbx)
    b6f6:	48 c1 ed 03          	shr    $0x3,%rbp
    b6fa:	48 8d 05 af ff ff ff 	lea    -0x51(%rip),%rax        # b6b0 <handle_client_request>
    b701:	4c 8d 8b c0 04 00 00 	lea    0x4c0(%rbx),%r9
    b708:	48 89 43 10          	mov    %rax,0x10(%rbx)
    b70c:	c7 85 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%rbp)
    b716:	c7 85 84 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff8084(%rbp)
    b720:	c7 85 88 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff8088(%rbp)
    b72a:	c7 85 8c 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff808c(%rbp)
    b734:	c7 85 90 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff8090(%rbp)
    b73e:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    b747:	48 89 84 24 b8 04 00 00 	mov    %rax,0x4b8(%rsp)
    b74f:	31 c0                	xor    %eax,%eax
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
    b751:	48 89 f8             	mov    %rdi,%rax
    b754:	48 c1 e8 03          	shr    $0x3,%rax
    b758:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    b75f:	0f 85 80 01 00 00    	jne    b8e5 <handle_client_request+0x235>
    for (int i = 0; i < dest_sz; i++) {
    b765:	49 8b 45 10          	mov    0x10(%r13),%rax
    b769:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
    b76d:	4c 8d 83 20 04 00 00 	lea    0x420(%rbx),%r8
    b774:	eb 1a                	jmp    b790 <handle_client_request+0xe0>
    b776:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    b780:	48 83 c7 01          	add    $0x1,%rdi
    b784:	48 89 c8             	mov    %rcx,%rax
    b787:	4c 39 c7             	cmp    %r8,%rdi
    b78a:	0f 84 f8 00 00 00    	je     b888 <handle_client_request+0x1d8>
        dest[i] = src[i];
    b790:	48 89 c2             	mov    %rax,%rdx
    b793:	48 89 c1             	mov    %rax,%rcx
    b796:	48 c1 ea 03          	shr    $0x3,%rdx
    b79a:	83 e1 07             	and    $0x7,%ecx
    b79d:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    b7a4:	38 ca                	cmp    %cl,%dl
    b7a6:	7f 08                	jg     b7b0 <handle_client_request+0x100>
    b7a8:	84 d2                	test   %dl,%dl
    b7aa:	0f 85 1b 01 00 00    	jne    b8cb <handle_client_request+0x21b>
    b7b0:	48 89 f9             	mov    %rdi,%rcx
    b7b3:	48 89 fe             	mov    %rdi,%rsi
    b7b6:	0f b6 10             	movzbl (%rax),%edx
    b7b9:	48 c1 e9 03          	shr    $0x3,%rcx
    b7bd:	83 e6 07             	and    $0x7,%esi
    b7c0:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    b7c7:	40 38 f1             	cmp    %sil,%cl
    b7ca:	7f 08                	jg     b7d4 <handle_client_request+0x124>
    b7cc:	84 c9                	test   %cl,%cl
    b7ce:	0f 85 ff 00 00 00    	jne    b8d3 <handle_client_request+0x223>
    b7d4:	88 17                	mov    %dl,(%rdi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    b7d6:	48 8d 48 01          	lea    0x1(%rax),%rcx
    b7da:	80 fa 0d             	cmp    $0xd,%dl
    b7dd:	75 a1                	jne    b780 <handle_client_request+0xd0>
    b7df:	48 89 ca             	mov    %rcx,%rdx
    b7e2:	48 89 ce             	mov    %rcx,%rsi
    b7e5:	48 c1 ea 03          	shr    $0x3,%rdx
    b7e9:	83 e6 07             	and    $0x7,%esi
    b7ec:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    b7f3:	40 38 f2             	cmp    %sil,%dl
    b7f6:	7f 08                	jg     b800 <handle_client_request+0x150>
    b7f8:	84 d2                	test   %dl,%dl
    b7fa:	0f 85 d8 00 00 00    	jne    b8d8 <handle_client_request+0x228>
    b800:	80 78 01 0a          	cmpb   $0xa,0x1(%rax)
    b804:	0f 85 76 ff ff ff    	jne    b780 <handle_client_request+0xd0>
            dest[i] = '\0';
    b80a:	c6 07 00             	movb   $0x0,(%rdi)
    handle_http_method(http_request, req->client_socket, ring);
    b80d:	49 8d 7d 08          	lea    0x8(%r13),%rdi
    b811:	48 89 f8             	mov    %rdi,%rax
    b814:	48 c1 e8 03          	shr    $0x3,%rax
    b818:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    b81f:	84 c0                	test   %al,%al
    b821:	74 08                	je     b82b <handle_client_request+0x17b>
    b823:	3c 03                	cmp    $0x3,%al
    b825:	0f 8e bf 00 00 00    	jle    b8ea <handle_client_request+0x23a>
    b82b:	41 8b 75 08          	mov    0x8(%r13),%esi
    b82f:	49 8d b9 60 fb ff ff 	lea    -0x4a0(%r9),%rdi
    b836:	4c 89 f2             	mov    %r14,%rdx
    b839:	e8 52 fb ff ff       	call   b390 <handle_http_method>
int handle_client_request(struct Request *req, struct io_uring *ring) {
    b83e:	49 39 dc             	cmp    %rbx,%r12
    b841:	0f 85 c3 00 00 00    	jne    b90a <handle_client_request+0x25a>
    b847:	c7 85 00 80 ff 7f 00 00 00 00 	movl   $0x0,0x7fff8000(%rbp)
    b851:	66 0f ef c0          	pxor   %xmm0,%xmm0
    b855:	0f 11 85 84 80 ff 7f 	movups %xmm0,0x7fff8084(%rbp)
}
    b85c:	48 8b 84 24 b8 04 00 00 	mov    0x4b8(%rsp),%rax
    b864:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    b86d:	75 71                	jne    b8e0 <handle_client_request+0x230>
    b86f:	48 81 c4 c0 04 00 00 	add    $0x4c0,%rsp
    b876:	31 c0                	xor    %eax,%eax
    b878:	5b                   	pop    %rbx
    b879:	5d                   	pop    %rbp
    b87a:	41 5c                	pop    %r12
    b87c:	41 5d                	pop    %r13
    b87e:	41 5e                	pop    %r14
    b880:	c3                   	ret
    b881:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        fprintf(stderr, "Malformed request\n");
    b888:	48 8d 3d 91 b2 00 00 	lea    0xb291(%rip),%rdi        # 16b20 <stderr@GLIBC_2.2.5>
    b88f:	48 89 f8             	mov    %rdi,%rax
    b892:	48 c1 e8 03          	shr    $0x3,%rax
    b896:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    b89d:	75 66                	jne    b905 <handle_client_request+0x255>
    b89f:	48 8b 0d 7a b2 00 00 	mov    0xb27a(%rip),%rcx        # 16b20 <stderr@GLIBC_2.2.5>
    b8a6:	ba 12 00 00 00       	mov    $0x12,%edx
    b8ab:	be 01 00 00 00       	mov    $0x1,%esi
    b8b0:	48 8d 3d e9 61 00 00 	lea    0x61e9(%rip),%rdi        # 11aa0 <_IO_stdin_used+0xaa0>
    b8b7:	e8 e4 8b ff ff       	call   44a0 <fwrite@plt>
        exit(1);
    b8bc:	e8 4f 8d ff ff       	call   4610 <__asan_handle_no_return@plt>
    b8c1:	bf 01 00 00 00       	mov    $0x1,%edi
    b8c6:	e8 45 8c ff ff       	call   4510 <exit@plt>
        dest[i] = src[i];
    b8cb:	48 89 c7             	mov    %rax,%rdi
    b8ce:	e8 bd 8e ff ff       	call   4790 <__asan_report_load1@plt>
    b8d3:	e8 f8 8e ff ff       	call   47d0 <__asan_report_store1@plt>
        if (src[i] == '\r' && src[i+1] == '\n') {
    b8d8:	48 89 cf             	mov    %rcx,%rdi
    b8db:	e8 b0 8e ff ff       	call   4790 <__asan_report_load1@plt>
}
    b8e0:	e8 cb 8d ff ff       	call   46b0 <__stack_chk_fail@plt>
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
    b8e5:	e8 f6 8b ff ff       	call   44e0 <__asan_report_load8@plt>
    handle_http_method(http_request, req->client_socket, ring);
    b8ea:	e8 61 8c ff ff       	call   4550 <__asan_report_load4@plt>
int handle_client_request(struct Request *req, struct io_uring *ring) {
    b8ef:	bf a0 04 00 00       	mov    $0x4a0,%edi
    b8f4:	e8 77 8e ff ff       	call   4770 <__asan_stack_malloc_5@plt>
    b8f9:	48 85 c0             	test   %rax,%rax
    b8fc:	48 0f 45 d8          	cmovne %rax,%rbx
    b900:	e9 d8 fd ff ff       	jmp    b6dd <handle_client_request+0x2d>
        fprintf(stderr, "Malformed request\n");
    b905:	e8 d6 8b ff ff       	call   44e0 <__asan_report_load8@plt>
int handle_client_request(struct Request *req, struct io_uring *ring) {
    b90a:	48 c7 03 0e 36 e0 45 	movq   $0x45e0360e,(%rbx)
    b911:	4c 89 e2             	mov    %r12,%rdx
    b914:	be a0 04 00 00       	mov    $0x4a0,%esi
    b919:	48 89 df             	mov    %rbx,%rdi
    b91c:	e8 5f 8d ff ff       	call   4680 <__asan_stack_free_5@plt>
    b921:	e9 36 ff ff ff       	jmp    b85c <handle_client_request+0x1ac>
    b926:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

000000000000b930 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    b930:	f3 0f 1e fa          	endbr64
    b934:	55                   	push   %rbp
    b935:	41 89 f8             	mov    %edi,%r8d
	unsigned int head, next = sq->sqe_tail + 1;
    b938:	48 8d 79 44          	lea    0x44(%rcx),%rdi
    b93c:	49 89 d1             	mov    %rdx,%r9
    b93f:	53                   	push   %rbx
    b940:	48 89 f8             	mov    %rdi,%rax
    b943:	48 89 cd             	mov    %rcx,%rbp
    b946:	48 c1 e8 03          	shr    $0x3,%rax
    b94a:	48 83 ec 08          	sub    $0x8,%rsp
    b94e:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    b955:	48 89 f8             	mov    %rdi,%rax
    b958:	83 e0 07             	and    $0x7,%eax
    b95b:	83 c0 03             	add    $0x3,%eax
    b95e:	38 d0                	cmp    %dl,%al
    b960:	7c 08                	jl     b96a <add_accept_request+0x3a>
    b962:	84 d2                	test   %dl,%dl
    b964:	0f 85 71 03 00 00    	jne    bcdb <add_accept_request+0x3ab>
	if (ring->flags & IORING_SETUP_SQE128)
    b96a:	48 8d bd c0 00 00 00 	lea    0xc0(%rbp),%rdi
	unsigned int head, next = sq->sqe_tail + 1;
    b971:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    b974:	48 89 fa             	mov    %rdi,%rdx
    b977:	48 c1 ea 03          	shr    $0x3,%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    b97b:	83 c0 01             	add    $0x1,%eax
	if (ring->flags & IORING_SETUP_SQE128)
    b97e:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    b985:	84 d2                	test   %dl,%dl
    b987:	74 09                	je     b992 <add_accept_request+0x62>
    b989:	80 fa 03             	cmp    $0x3,%dl
    b98c:	0f 8e 44 03 00 00    	jle    bcd6 <add_accept_request+0x3a6>
    b992:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    b998:	48 89 ef             	mov    %rbp,%rdi
    b99b:	48 c1 ef 03          	shr    $0x3,%rdi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    b99f:	89 ca                	mov    %ecx,%edx
    b9a1:	83 e2 02             	and    $0x2,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    b9a4:	80 bf 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdi)
    b9ab:	0f 85 7e 03 00 00    	jne    bd2f <add_accept_request+0x3ff>
    b9b1:	48 8b 7d 00          	mov    0x0(%rbp),%rdi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    b9b5:	85 d2                	test   %edx,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    b9b7:	48 89 fa             	mov    %rdi,%rdx
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    b9ba:	0f 85 f0 02 00 00    	jne    bcb0 <add_accept_request+0x380>
		head = IO_URING_READ_ONCE(*sq->khead);
    b9c0:	48 c1 ea 03          	shr    $0x3,%rdx
    b9c4:	44 0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%r10d
    b9cc:	48 89 fa             	mov    %rdi,%rdx
    b9cf:	83 e2 07             	and    $0x7,%edx
    b9d2:	83 c2 03             	add    $0x3,%edx
    b9d5:	44 38 d2             	cmp    %r10b,%dl
    b9d8:	7c 09                	jl     b9e3 <add_accept_request+0xb3>
    b9da:	45 84 d2             	test   %r10b,%r10b
    b9dd:	0f 85 47 03 00 00    	jne    bd2a <add_accept_request+0x3fa>
    b9e3:	8b 17                	mov    (%rdi),%edx
	if (next - head <= sq->ring_entries) {
    b9e5:	48 8d 7d 5c          	lea    0x5c(%rbp),%rdi
    b9e9:	41 89 c3             	mov    %eax,%r11d
    b9ec:	41 29 d3             	sub    %edx,%r11d
    b9ef:	48 89 fa             	mov    %rdi,%rdx
    b9f2:	48 c1 ea 03          	shr    $0x3,%rdx
    b9f6:	44 0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%r10d
    b9fe:	48 89 fa             	mov    %rdi,%rdx
    ba01:	83 e2 07             	and    $0x7,%edx
    ba04:	83 c2 03             	add    $0x3,%edx
    ba07:	44 38 d2             	cmp    %r10b,%dl
    ba0a:	7c 09                	jl     ba15 <add_accept_request+0xe5>
    ba0c:	45 84 d2             	test   %r10b,%r10b
    ba0f:	0f 85 cb 02 00 00    	jne    bce0 <add_accept_request+0x3b0>
    ba15:	44 39 5d 5c          	cmp    %r11d,0x5c(%rbp)
    ba19:	0f 82 94 8f ff ff    	jb     49b3 <add_accept_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    ba1f:	48 8d 7d 38          	lea    0x38(%rbp),%rdi
    ba23:	48 89 fa             	mov    %rdi,%rdx
    ba26:	48 c1 ea 03          	shr    $0x3,%rdx
    ba2a:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    ba31:	0f 85 19 03 00 00    	jne    bd50 <add_accept_request+0x420>
    ba37:	4c 8d 55 58          	lea    0x58(%rbp),%r10
    ba3b:	48 8b 5d 38          	mov    0x38(%rbp),%rbx
    ba3f:	8b 55 44             	mov    0x44(%rbp),%edx
    ba42:	4c 89 d7             	mov    %r10,%rdi
    ba45:	48 c1 ef 03          	shr    $0x3,%rdi
    ba49:	0f b6 bf 00 80 ff 7f 	movzbl 0x7fff8000(%rdi),%edi
    ba50:	40 84 ff             	test   %dil,%dil
    ba53:	74 0a                	je     ba5f <add_accept_request+0x12f>
    ba55:	40 80 ff 03          	cmp    $0x3,%dil
    ba59:	0f 8e 98 02 00 00    	jle    bcf7 <add_accept_request+0x3c7>
	if (ring->flags & IORING_SETUP_SQE128)
    ba5f:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    ba62:	23 55 58             	and    0x58(%rbp),%edx
		sq->sqe_tail = next;
    ba65:	89 45 44             	mov    %eax,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    ba68:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    ba6b:	d3 e2                	shl    %cl,%edx
    ba6d:	48 c1 e2 06          	shl    $0x6,%rdx
    ba71:	48 01 d3             	add    %rdx,%rbx
	sqe->opcode = (__u8) op;
    ba74:	48 89 d8             	mov    %rbx,%rax
    ba77:	48 c1 e8 03          	shr    $0x3,%rax
    ba7b:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    ba82:	84 c0                	test   %al,%al
    ba84:	74 06                	je     ba8c <add_accept_request+0x15c>
    ba86:	0f 8e 5e 02 00 00    	jle    bcea <add_accept_request+0x3ba>
	sqe->flags = 0;
    ba8c:	48 8d 7b 01          	lea    0x1(%rbx),%rdi
	sqe->opcode = (__u8) op;
    ba90:	c6 03 0d             	movb   $0xd,(%rbx)
	sqe->flags = 0;
    ba93:	48 89 f8             	mov    %rdi,%rax
    ba96:	48 89 fa             	mov    %rdi,%rdx
    ba99:	48 c1 e8 03          	shr    $0x3,%rax
    ba9d:	83 e2 07             	and    $0x7,%edx
    baa0:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    baa7:	38 d0                	cmp    %dl,%al
    baa9:	7f 08                	jg     bab3 <add_accept_request+0x183>
    baab:	84 c0                	test   %al,%al
    baad:	0f 85 32 02 00 00    	jne    bce5 <add_accept_request+0x3b5>
	sqe->ioprio = 0;
    bab3:	48 8d 7b 02          	lea    0x2(%rbx),%rdi
	sqe->flags = 0;
    bab7:	c6 43 01 00          	movb   $0x0,0x1(%rbx)
	sqe->ioprio = 0;
    babb:	48 89 f8             	mov    %rdi,%rax
    babe:	48 c1 e8 03          	shr    $0x3,%rax
    bac2:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    bac9:	48 89 f8             	mov    %rdi,%rax
    bacc:	83 e0 07             	and    $0x7,%eax
    bacf:	83 c0 01             	add    $0x1,%eax
    bad2:	38 d0                	cmp    %dl,%al
    bad4:	7c 08                	jl     bade <add_accept_request+0x1ae>
    bad6:	84 d2                	test   %dl,%dl
    bad8:	0f 85 26 02 00 00    	jne    bd04 <add_accept_request+0x3d4>
	sqe->fd = fd;
    bade:	48 8d 7b 04          	lea    0x4(%rbx),%rdi
	sqe->ioprio = 0;
    bae2:	31 c9                	xor    %ecx,%ecx
	sqe->fd = fd;
    bae4:	48 89 f8             	mov    %rdi,%rax
	sqe->ioprio = 0;
    bae7:	66 89 4b 02          	mov    %cx,0x2(%rbx)
	sqe->fd = fd;
    baeb:	48 c1 e8 03          	shr    $0x3,%rax
    baef:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    baf6:	48 89 f8             	mov    %rdi,%rax
    baf9:	83 e0 07             	and    $0x7,%eax
    bafc:	83 c0 03             	add    $0x3,%eax
    baff:	38 d0                	cmp    %dl,%al
    bb01:	7c 08                	jl     bb0b <add_accept_request+0x1db>
    bb03:	84 d2                	test   %dl,%dl
    bb05:	0f 85 f4 01 00 00    	jne    bcff <add_accept_request+0x3cf>
	sqe->off = offset;
    bb0b:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
	sqe->fd = fd;
    bb0f:	44 89 43 04          	mov    %r8d,0x4(%rbx)
	sqe->off = offset;
    bb13:	48 89 f8             	mov    %rdi,%rax
    bb16:	48 c1 e8 03          	shr    $0x3,%rax
    bb1a:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    bb21:	0f 85 24 02 00 00    	jne    bd4b <add_accept_request+0x41b>
	sqe->addr = (unsigned long) addr;
    bb27:	48 8d 7b 10          	lea    0x10(%rbx),%rdi
	sqe->off = offset;
    bb2b:	4c 89 4b 08          	mov    %r9,0x8(%rbx)
	sqe->addr = (unsigned long) addr;
    bb2f:	48 89 f8             	mov    %rdi,%rax
    bb32:	48 c1 e8 03          	shr    $0x3,%rax
    bb36:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    bb3d:	0f 85 03 02 00 00    	jne    bd46 <add_accept_request+0x416>
	sqe->len = len;
    bb43:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
	sqe->addr = (unsigned long) addr;
    bb47:	48 89 73 10          	mov    %rsi,0x10(%rbx)
	sqe->len = len;
    bb4b:	48 89 f8             	mov    %rdi,%rax
    bb4e:	48 c1 e8 03          	shr    $0x3,%rax
    bb52:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    bb59:	84 c0                	test   %al,%al
    bb5b:	74 08                	je     bb65 <add_accept_request+0x235>
    bb5d:	3c 03                	cmp    $0x3,%al
    bb5f:	0f 8e 8d 01 00 00    	jle    bcf2 <add_accept_request+0x3c2>
	sqe->buf_index = 0;
    bb65:	48 8d 7b 28          	lea    0x28(%rbx),%rdi
	sqe->len = len;
    bb69:	c7 43 18 00 00 00 00 	movl   $0x0,0x18(%rbx)
	sqe->buf_index = 0;
    bb70:	48 89 f8             	mov    %rdi,%rax
    bb73:	48 c1 e8 03          	shr    $0x3,%rax
    bb77:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    bb7e:	84 c0                	test   %al,%al
    bb80:	74 08                	je     bb8a <add_accept_request+0x25a>
    bb82:	3c 01                	cmp    $0x1,%al
    bb84:	0f 8e 96 01 00 00    	jle    bd20 <add_accept_request+0x3f0>
	sqe->personality = 0;
    bb8a:	48 8d 7b 2a          	lea    0x2a(%rbx),%rdi
	sqe->buf_index = 0;
    bb8e:	31 d2                	xor    %edx,%edx
	sqe->personality = 0;
    bb90:	48 89 f8             	mov    %rdi,%rax
	sqe->buf_index = 0;
    bb93:	66 89 53 28          	mov    %dx,0x28(%rbx)
	sqe->personality = 0;
    bb97:	48 c1 e8 03          	shr    $0x3,%rax
    bb9b:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    bba2:	48 89 f8             	mov    %rdi,%rax
    bba5:	83 e0 07             	and    $0x7,%eax
    bba8:	83 c0 01             	add    $0x1,%eax
    bbab:	38 d0                	cmp    %dl,%al
    bbad:	7c 08                	jl     bbb7 <add_accept_request+0x287>
    bbaf:	84 d2                	test   %dl,%dl
    bbb1:	0f 85 64 01 00 00    	jne    bd1b <add_accept_request+0x3eb>
    bbb7:	31 c0                	xor    %eax,%eax
	sqe->file_index = 0;
    bbb9:	48 8d 7b 2c          	lea    0x2c(%rbx),%rdi
	sqe->personality = 0;
    bbbd:	66 89 43 2a          	mov    %ax,0x2a(%rbx)
	sqe->file_index = 0;
    bbc1:	48 89 f8             	mov    %rdi,%rax
    bbc4:	48 c1 e8 03          	shr    $0x3,%rax
    bbc8:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    bbcf:	48 89 f8             	mov    %rdi,%rax
    bbd2:	83 e0 07             	and    $0x7,%eax
    bbd5:	83 c0 03             	add    $0x3,%eax
    bbd8:	38 d0                	cmp    %dl,%al
    bbda:	7c 08                	jl     bbe4 <add_accept_request+0x2b4>
    bbdc:	84 d2                	test   %dl,%dl
    bbde:	0f 85 32 01 00 00    	jne    bd16 <add_accept_request+0x3e6>
	sqe->addr3 = 0;
    bbe4:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
	sqe->file_index = 0;
    bbe8:	c7 43 2c 00 00 00 00 	movl   $0x0,0x2c(%rbx)
	sqe->addr3 = 0;
    bbef:	48 89 f8             	mov    %rdi,%rax
    bbf2:	48 c1 e8 03          	shr    $0x3,%rax
    bbf6:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    bbfd:	0f 85 3e 01 00 00    	jne    bd41 <add_accept_request+0x411>
	sqe->__pad2[0] = 0;
    bc03:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
	sqe->addr3 = 0;
    bc07:	48 c7 43 30 00 00 00 00 	movq   $0x0,0x30(%rbx)
	sqe->__pad2[0] = 0;
    bc0f:	48 89 f8             	mov    %rdi,%rax
    bc12:	48 c1 e8 03          	shr    $0x3,%rax
    bc16:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    bc1d:	0f 85 19 01 00 00    	jne    bd3c <add_accept_request+0x40c>
	sqe->accept_flags = (__u32) flags;
    bc23:	48 8d 7b 1c          	lea    0x1c(%rbx),%rdi
	sqe->__pad2[0] = 0;
    bc27:	48 c7 43 38 00 00 00 00 	movq   $0x0,0x38(%rbx)
	sqe->accept_flags = (__u32) flags;
    bc2f:	48 89 f8             	mov    %rdi,%rax
    bc32:	48 c1 e8 03          	shr    $0x3,%rax
    bc36:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    bc3d:	48 89 f8             	mov    %rdi,%rax
    bc40:	83 e0 07             	and    $0x7,%eax
    bc43:	83 c0 03             	add    $0x3,%eax
    bc46:	38 d0                	cmp    %dl,%al
    bc48:	7c 08                	jl     bc52 <add_accept_request+0x322>
    bc4a:	84 d2                	test   %dl,%dl
    bc4c:	0f 85 bf 00 00 00    	jne    bd11 <add_accept_request+0x3e1>
    bc52:	c7 43 1c 00 00 00 00 	movl   $0x0,0x1c(%rbx)
  struct Request *req = malloc(sizeof(*req));
    bc59:	bf 10 00 00 00       	mov    $0x10,%edi
    bc5e:	e8 2d 89 ff ff       	call   4590 <malloc@plt>
  req->event_type = EVENT_TYPE_ACCEPT;
    bc63:	48 89 c2             	mov    %rax,%rdx
    bc66:	48 c1 ea 03          	shr    $0x3,%rdx
    bc6a:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    bc71:	84 d2                	test   %dl,%dl
    bc73:	74 09                	je     bc7e <add_accept_request+0x34e>
    bc75:	80 fa 03             	cmp    $0x3,%dl
    bc78:	0f 8e 8b 00 00 00    	jle    bd09 <add_accept_request+0x3d9>
	sqe->user_data = (unsigned long) data;
    bc7e:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
    bc82:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    bc88:	48 89 fa             	mov    %rdi,%rdx
    bc8b:	48 c1 ea 03          	shr    $0x3,%rdx
    bc8f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    bc96:	0f 85 9b 00 00 00    	jne    bd37 <add_accept_request+0x407>
    bc9c:	48 89 43 20          	mov    %rax,0x20(%rbx)
}
    bca0:	48 83 c4 08          	add    $0x8,%rsp
  io_uring_submit(ring);
    bca4:	48 89 ef             	mov    %rbp,%rdi
}
    bca7:	5b                   	pop    %rbx
    bca8:	5d                   	pop    %rbp
  io_uring_submit(ring);
    bca9:	e9 b2 89 ff ff       	jmp    4660 <io_uring_submit@plt>
    bcae:	66 90                	xchg   %ax,%ax
		head = io_uring_smp_load_acquire(sq->khead);
    bcb0:	48 c1 ea 03          	shr    $0x3,%rdx
    bcb4:	44 0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%r10d
    bcbc:	48 89 fa             	mov    %rdi,%rdx
    bcbf:	83 e2 07             	and    $0x7,%edx
    bcc2:	83 c2 03             	add    $0x3,%edx
    bcc5:	44 38 d2             	cmp    %r10b,%dl
    bcc8:	7c 05                	jl     bccf <add_accept_request+0x39f>
    bcca:	45 84 d2             	test   %r10b,%r10b
    bccd:	75 56                	jne    bd25 <add_accept_request+0x3f5>
    bccf:	8b 17                	mov    (%rdi),%edx
    bcd1:	e9 0f fd ff ff       	jmp    b9e5 <add_accept_request+0xb5>
	if (ring->flags & IORING_SETUP_SQE128)
    bcd6:	e8 75 88 ff ff       	call   4550 <__asan_report_load4@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    bcdb:	e8 70 88 ff ff       	call   4550 <__asan_report_load4@plt>
	if (next - head <= sq->ring_entries) {
    bce0:	e8 6b 88 ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->flags = 0;
    bce5:	e8 e6 8a ff ff       	call   47d0 <__asan_report_store1@plt>
	sqe->opcode = (__u8) op;
    bcea:	48 89 df             	mov    %rbx,%rdi
    bced:	e8 de 8a ff ff       	call   47d0 <__asan_report_store1@plt>
	sqe->len = len;
    bcf2:	e8 c9 89 ff ff       	call   46c0 <__asan_report_store4@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    bcf7:	4c 89 d7             	mov    %r10,%rdi
    bcfa:	e8 51 88 ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->fd = fd;
    bcff:	e8 bc 89 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->ioprio = 0;
    bd04:	e8 f7 87 ff ff       	call   4500 <__asan_report_store2@plt>
  req->event_type = EVENT_TYPE_ACCEPT;
    bd09:	48 89 c7             	mov    %rax,%rdi
    bd0c:	e8 af 89 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->accept_flags = (__u32) flags;
    bd11:	e8 aa 89 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->file_index = 0;
    bd16:	e8 a5 89 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->personality = 0;
    bd1b:	e8 e0 87 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->buf_index = 0;
    bd20:	e8 db 87 ff ff       	call   4500 <__asan_report_store2@plt>
		head = io_uring_smp_load_acquire(sq->khead);
    bd25:	e8 26 88 ff ff       	call   4550 <__asan_report_load4@plt>
		head = IO_URING_READ_ONCE(*sq->khead);
    bd2a:	e8 21 88 ff ff       	call   4550 <__asan_report_load4@plt>
    bd2f:	48 89 ef             	mov    %rbp,%rdi
    bd32:	e8 a9 87 ff ff       	call   44e0 <__asan_report_load8@plt>
	sqe->user_data = (unsigned long) data;
    bd37:	e8 94 89 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->__pad2[0] = 0;
    bd3c:	e8 8f 89 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->addr3 = 0;
    bd41:	e8 8a 89 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->addr = (unsigned long) addr;
    bd46:	e8 85 89 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->off = offset;
    bd4b:	e8 80 89 ff ff       	call   46d0 <__asan_report_store8@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    bd50:	e8 8b 87 ff ff       	call   44e0 <__asan_report_load8@plt>
    bd55:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

000000000000bd60 <io_thread>:
void* io_thread(void *arg) {
    bd60:	f3 0f 1e fa          	endbr64
    bd64:	41 57                	push   %r15
    bd66:	41 56                	push   %r14
    bd68:	41 55                	push   %r13
    bd6a:	41 54                	push   %r12
    bd6c:	55                   	push   %rbp
    bd6d:	53                   	push   %rbx
    bd6e:	48 81 ec 18 07 00 00 	sub    $0x718,%rsp
    bd75:	44 8b 3d 84 ad 00 00 	mov    0xad84(%rip),%r15d        # 16b00 <__asan_option_detect_stack_use_after_return@@Base>
    bd7c:	48 8d 84 24 b0 00 00 00 	lea    0xb0(%rsp),%rax
    bd84:	48 89 7c 24 18       	mov    %rdi,0x18(%rsp)
    bd89:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    bd8e:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
    bd96:	45 85 ff             	test   %r15d,%r15d
    bd99:	0f 85 77 17 00 00    	jne    d516 <io_thread+0x17b6>
    bd9f:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    bda4:	48 8d 35 85 71 00 00 	lea    0x7185(%rip),%rsi        # 12f30 <_IO_stdin_used+0x1f30>
    bdab:	48 89 c5             	mov    %rax,%rbp
    bdae:	48 89 70 08          	mov    %rsi,0x8(%rax)
    bdb2:	48 8d 35 a7 ff ff ff 	lea    -0x59(%rip),%rsi        # bd60 <io_thread>
    bdb9:	48 8d 98 60 06 00 00 	lea    0x660(%rax),%rbx
    bdc0:	48 c1 ed 03          	shr    $0x3,%rbp
    bdc4:	48 c7 00 b3 8a b5 41 	movq   $0x41b58ab3,(%rax)
    bdcb:	48 89 70 10          	mov    %rsi,0x10(%rax)
    bdcf:	c7 85 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%rbp)
    bdd9:	c7 85 04 80 ff 7f 04 f2 04 f2 	movl   $0xf204f204,0x7fff8004(%rbp)
    bde3:	c7 85 08 80 ff 7f 00 f2 f2 f2 	movl   $0xf2f2f200,0x7fff8008(%rbp)
    bded:	c7 85 0c 80 ff 7f 00 00 f2 f2 	movl   $0xf2f20000,0x7fff800c(%rbp)
    bdf7:	c7 85 10 80 ff 7f 00 00 f2 f2 	movl   $0xf2f20000,0x7fff8010(%rbp)
    be01:	c7 85 2c 80 ff 7f 00 00 00 f2 	movl   $0xf2000000,0x7fff802c(%rbp)
    be0b:	c7 85 30 80 ff 7f f2 f2 f2 f2 	movl   $0xf2f2f2f2,0x7fff8030(%rbp)
    be15:	c7 85 34 80 ff 7f f2 f2 f2 f2 	movl   $0xf2f2f2f2,0x7fff8034(%rbp)
    be1f:	c7 85 b8 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff80b8(%rbp)
    be29:	c7 85 bc 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff80bc(%rbp)
    be33:	c7 85 c0 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff80c0(%rbp)
    be3d:	c7 85 c4 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff80c4(%rbp)
  struct io_uring ring = *data->ring;
    be47:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    be50:	48 89 84 24 08 07 00 00 	mov    %rax,0x708(%rsp)
    be58:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    be5d:	4c 8d 60 58          	lea    0x58(%rax),%r12
    be61:	4d 89 e5             	mov    %r12,%r13
    be64:	49 c1 ed 03          	shr    $0x3,%r13
    be68:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    be70:	0f 85 98 16 00 00    	jne    d50e <io_thread+0x17ae>
    be76:	48 8b 74 24 58       	mov    0x58(%rsp),%rsi
    be7b:	48 8b 78 58          	mov    0x58(%rax),%rdi
    be7f:	48 8d 8e a0 00 00 00 	lea    0xa0(%rsi),%rcx
    be86:	48 89 c8             	mov    %rcx,%rax
    be89:	48 c1 e8 03          	shr    $0x3,%rax
    be8d:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    be94:	48 8d 86 77 01 00 00 	lea    0x177(%rsi),%rax
    be9b:	48 89 c6             	mov    %rax,%rsi
    be9e:	83 e0 07             	and    $0x7,%eax
    bea1:	48 c1 ee 03          	shr    $0x3,%rsi
    bea5:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    beac:	40 38 c6             	cmp    %al,%sil
    beaf:	41 0f 9e c0          	setle  %r8b
    beb3:	40 84 f6             	test   %sil,%sil
    beb6:	0f 95 c0             	setne  %al
    beb9:	41 84 c0             	test   %al,%r8b
    bebc:	0f 85 3f 16 00 00    	jne    d501 <io_thread+0x17a1>
    bec2:	84 d2                	test   %dl,%dl
    bec4:	40 0f 95 c6          	setne  %sil
    bec8:	0f 9e c0             	setle  %al
    becb:	40 84 c6             	test   %al,%sil
    bece:	0f 85 2d 16 00 00    	jne    d501 <io_thread+0x17a1>
    bed4:	48 89 f8             	mov    %rdi,%rax
    bed7:	48 c1 e8 03          	shr    $0x3,%rax
    bedb:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    bee2:	48 8d 87 d7 00 00 00 	lea    0xd7(%rdi),%rax
    bee9:	48 89 c6             	mov    %rax,%rsi
    beec:	83 e0 07             	and    $0x7,%eax
    beef:	48 c1 ee 03          	shr    $0x3,%rsi
    bef3:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    befa:	40 38 c6             	cmp    %al,%sil
    befd:	41 0f 9e c0          	setle  %r8b
    bf01:	40 84 f6             	test   %sil,%sil
    bf04:	0f 95 c0             	setne  %al
    bf07:	41 84 c0             	test   %al,%r8b
    bf0a:	0f 85 e7 15 00 00    	jne    d4f7 <io_thread+0x1797>
    bf10:	84 d2                	test   %dl,%dl
    bf12:	40 0f 95 c6          	setne  %sil
    bf16:	0f 9e c0             	setle  %al
    bf19:	40 84 c6             	test   %al,%sil
    bf1c:	0f 85 d5 15 00 00    	jne    d4f7 <io_thread+0x1797>
    bf22:	f3 0f 6f 0f          	movdqu (%rdi),%xmm1
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    bf26:	31 d2                	xor    %edx,%edx
    bf28:	48 89 ce             	mov    %rcx,%rsi
  struct io_uring ring = *data->ring;
    bf2b:	0f 29 8b 40 fa ff ff 	movaps %xmm1,-0x5c0(%rbx)
    bf32:	f3 0f 6f 57 10       	movdqu 0x10(%rdi),%xmm2
    bf37:	0f 29 93 50 fa ff ff 	movaps %xmm2,-0x5b0(%rbx)
    bf3e:	f3 0f 6f 5f 20       	movdqu 0x20(%rdi),%xmm3
    bf43:	0f 29 9b 60 fa ff ff 	movaps %xmm3,-0x5a0(%rbx)
    bf4a:	f3 0f 6f 67 30       	movdqu 0x30(%rdi),%xmm4
    bf4f:	0f 29 a3 70 fa ff ff 	movaps %xmm4,-0x590(%rbx)
    bf56:	f3 0f 6f 6f 40       	movdqu 0x40(%rdi),%xmm5
    bf5b:	0f 29 ab 80 fa ff ff 	movaps %xmm5,-0x580(%rbx)
    bf62:	f3 0f 6f 77 50       	movdqu 0x50(%rdi),%xmm6
    bf67:	0f 29 b3 90 fa ff ff 	movaps %xmm6,-0x570(%rbx)
    bf6e:	f3 0f 6f 7f 60       	movdqu 0x60(%rdi),%xmm7
    bf73:	0f 29 bb a0 fa ff ff 	movaps %xmm7,-0x560(%rbx)
    bf7a:	f3 0f 6f 47 70       	movdqu 0x70(%rdi),%xmm0
    bf7f:	0f 29 83 b0 fa ff ff 	movaps %xmm0,-0x550(%rbx)
    bf86:	f3 0f 6f 8f 80 00 00 00 	movdqu 0x80(%rdi),%xmm1
    bf8e:	0f 29 8b c0 fa ff ff 	movaps %xmm1,-0x540(%rbx)
    bf95:	f3 0f 6f 97 90 00 00 00 	movdqu 0x90(%rdi),%xmm2
    bf9d:	0f 29 93 d0 fa ff ff 	movaps %xmm2,-0x530(%rbx)
    bfa4:	f3 0f 6f 9f a0 00 00 00 	movdqu 0xa0(%rdi),%xmm3
    bfac:	0f 29 9b e0 fa ff ff 	movaps %xmm3,-0x520(%rbx)
    bfb3:	f3 0f 6f a7 b0 00 00 00 	movdqu 0xb0(%rdi),%xmm4
    bfbb:	0f 29 a3 f0 fa ff ff 	movaps %xmm4,-0x510(%rbx)
    bfc2:	f3 0f 6f af c0 00 00 00 	movdqu 0xc0(%rdi),%xmm5
    bfca:	0f 29 ab 00 fb ff ff 	movaps %xmm5,-0x500(%rbx)
    bfd1:	48 8b 87 d0 00 00 00 	mov    0xd0(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    bfd8:	bf 00 01 00 00       	mov    $0x100,%edi
  struct io_uring ring = *data->ring;
    bfdd:	48 89 83 10 fb ff ff 	mov    %rax,-0x4f0(%rbx)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    bfe4:	e8 87 84 ff ff       	call   4470 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    bfe9:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    bff1:	0f 85 f8 14 00 00    	jne    d4ef <io_thread+0x178f>
    bff7:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    bffc:	31 f6                	xor    %esi,%esi
    bffe:	48 8b 78 58          	mov    0x58(%rax),%rdi
    c002:	e8 29 86 ff ff       	call   4630 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    c007:	31 d2                	xor    %edx,%edx
    c009:	be 01 00 00 00       	mov    $0x1,%esi
    c00e:	bf 02 00 00 00       	mov    $0x2,%edi
    c013:	e8 78 86 ff ff       	call   4690 <socket@plt>
    c018:	89 44 24 44          	mov    %eax,0x44(%rsp)
  if (sock == -1)
    c01c:	83 f8 ff             	cmp    $0xffffffff,%eax
    c01f:	0f 84 28 8a ff ff    	je     4a4d <io_thread.cold+0x7b>
  int enable = 1;
    c025:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    c02a:	48 8d 78 20          	lea    0x20(%rax),%rdi
    c02e:	48 89 f8             	mov    %rdi,%rax
    c031:	48 c1 e8 03          	shr    $0x3,%rax
    c035:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    c03c:	84 c0                	test   %al,%al
    c03e:	74 08                	je     c048 <io_thread+0x2e8>
    c040:	3c 03                	cmp    $0x3,%al
    c042:	0f 8e 80 15 00 00    	jle    d5c8 <io_thread+0x1868>
  if (setsockopt(sock,
    c048:	8b 7c 24 44          	mov    0x44(%rsp),%edi
    c04c:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    c052:	ba 02 00 00 00       	mov    $0x2,%edx
    c057:	48 8d 8b c0 f9 ff ff 	lea    -0x640(%rbx),%rcx
  int enable = 1;
    c05e:	c7 83 c0 f9 ff ff 01 00 00 00 	movl   $0x1,-0x640(%rbx)
  if (setsockopt(sock,
    c068:	be 01 00 00 00       	mov    $0x1,%esi
    c06d:	e8 4e 85 ff ff       	call   45c0 <setsockopt@plt>
    c072:	85 c0                	test   %eax,%eax
    c074:	0f 88 81 89 ff ff    	js     49fb <io_thread.cold+0x29>
  return __builtin___memset_chk (__dest, __ch, __len,
    c07a:	4c 8d a3 00 fa ff ff 	lea    -0x600(%rbx),%r12
    c081:	48 8d bb 04 fa ff ff 	lea    -0x5fc(%rbx),%rdi
    c088:	ba 0c 00 00 00       	mov    $0xc,%edx
    c08d:	31 f6                	xor    %esi,%esi
    c08f:	e8 0c 86 ff ff       	call   46a0 <memset@plt>
  srv_addr.sin_family = AF_INET;
    c094:	4c 89 e0             	mov    %r12,%rax
    c097:	48 c1 e8 03          	shr    $0x3,%rax
    c09b:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    c0a2:	84 c0                	test   %al,%al
    c0a4:	74 08                	je     c0ae <io_thread+0x34e>
    c0a6:	3c 01                	cmp    $0x1,%al
    c0a8:	0f 8e 3e 15 00 00    	jle    d5ec <io_thread+0x188c>
  srv_addr.sin_port = htons(port);
    c0ae:	48 8d bb 02 fa ff ff 	lea    -0x5fe(%rbx),%rdi
  srv_addr.sin_family = AF_INET;
    c0b5:	41 be 02 00 00 00    	mov    $0x2,%r14d
  srv_addr.sin_port = htons(port);
    c0bb:	48 89 f8             	mov    %rdi,%rax
  srv_addr.sin_family = AF_INET;
    c0be:	66 44 89 b3 00 fa ff ff 	mov    %r14w,-0x600(%rbx)
  srv_addr.sin_port = htons(port);
    c0c6:	48 c1 e8 03          	shr    $0x3,%rax
    c0ca:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    c0d1:	48 89 f8             	mov    %rdi,%rax
    c0d4:	83 e0 07             	and    $0x7,%eax
    c0d7:	83 c0 01             	add    $0x1,%eax
    c0da:	38 d0                	cmp    %dl,%al
    c0dc:	7c 08                	jl     c0e6 <io_thread+0x386>
    c0de:	84 d2                	test   %dl,%dl
    c0e0:	0f 85 01 15 00 00    	jne    d5e7 <io_thread+0x1887>
  if (bind(sock,
    c0e6:	8b 7c 24 44          	mov    0x44(%rsp),%edi
  srv_addr.sin_port = htons(port);
    c0ea:	41 bd 18 db ff ff    	mov    $0xffffdb18,%r13d
  if (bind(sock,
    c0f0:	ba 10 00 00 00       	mov    $0x10,%edx
    c0f5:	4c 89 e6             	mov    %r12,%rsi
  srv_addr.sin_port = htons(port);
    c0f8:	66 44 89 ab 02 fa ff ff 	mov    %r13w,-0x5fe(%rbx)
  if (bind(sock,
    c100:	e8 7b 86 ff ff       	call   4780 <bind@plt>
    c105:	85 c0                	test   %eax,%eax
    c107:	0f 88 17 89 ff ff    	js     4a24 <io_thread.cold+0x52>
  if (listen(sock, 10) < 0) {
    c10d:	8b 7c 24 44          	mov    0x44(%rsp),%edi
    c111:	be 0a 00 00 00       	mov    $0xa,%esi
    c116:	e8 05 85 ff ff       	call   4620 <listen@plt>
    c11b:	85 c0                	test   %eax,%eax
    c11d:	0f 88 c7 88 ff ff    	js     49ea <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    c123:	ba db 18 00 00       	mov    $0x18db,%edx
    c128:	48 8d 35 b1 5a 00 00 	lea    0x5ab1(%rip),%rsi        # 11be0 <_IO_stdin_used+0xbe0>
    c12f:	bf 01 00 00 00       	mov    $0x1,%edi
    c134:	31 c0                	xor    %eax,%eax
    c136:	e8 e5 83 ff ff       	call   4520 <__printf_chk@plt>
  socklen_t client_addr_len = sizeof(client_addr);
    c13b:	48 8d 83 d0 f9 ff ff 	lea    -0x630(%rbx),%rax
    c142:	48 89 84 24 80 00 00 00 	mov    %rax,0x80(%rsp)
    c14a:	48 c1 e8 03          	shr    $0x3,%rax
    c14e:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    c155:	84 c0                	test   %al,%al
    c157:	74 08                	je     c161 <io_thread+0x401>
    c159:	3c 03                	cmp    $0x3,%al
    c15b:	0f 8e 5a 14 00 00    	jle    d5bb <io_thread+0x185b>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    c161:	48 8d 83 20 fa ff ff 	lea    -0x5e0(%rbx),%rax
    c168:	48 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%rdx
    c170:	8b 7c 24 44          	mov    0x44(%rsp),%edi
    c174:	48 8d 8b 40 fa ff ff 	lea    -0x5c0(%rbx),%rcx
    c17b:	48 89 c6             	mov    %rax,%rsi
    c17e:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    c183:	c7 83 d0 f9 ff ff 10 00 00 00 	movl   $0x10,-0x630(%rbx)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    c18d:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
    c195:	e8 96 f7 ff ff       	call   b930 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    c19a:	bf 01 00 00 00       	mov    $0x1,%edi
    c19f:	be 10 00 00 00       	mov    $0x10,%esi
    c1a4:	e8 b7 82 ff ff       	call   4460 <calloc@plt>
    void *buf = malloc(size);
    c1a9:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    c1ae:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    void *buf = malloc(size);
    c1b3:	e8 d8 83 ff ff       	call   4590 <malloc@plt>
    if (!buf) {
    c1b8:	48 85 c0             	test   %rax,%rax
    c1bb:	0f 84 b7 13 00 00    	je     d578 <io_thread+0x1818>
  iov->iov_base = zh_malloc(10);
    c1c1:	48 8b 54 24 28       	mov    0x28(%rsp),%rdx
    c1c6:	48 c1 ea 03          	shr    $0x3,%rdx
    c1ca:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    c1d1:	0f 85 97 13 00 00    	jne    d56e <io_thread+0x180e>
    c1d7:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
  iov->iov_len = 10;
    c1dc:	48 8d 7e 08          	lea    0x8(%rsi),%rdi
  iov->iov_base = zh_malloc(10);
    c1e0:	48 89 06             	mov    %rax,(%rsi)
  iov->iov_len = 10;
    c1e3:	48 89 f8             	mov    %rdi,%rax
    c1e6:	48 c1 e8 03          	shr    $0x3,%rax
    c1ea:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c1f1:	0f 85 72 13 00 00    	jne    d569 <io_thread+0x1809>
    c1f7:	48 c7 46 08 0a 00 00 00 	movq   $0xa,0x8(%rsi)
	unsigned int head, next = sq->sqe_tail + 1;
    c1ff:	48 8d b3 84 fa ff ff 	lea    -0x57c(%rbx),%rsi
    c206:	48 89 f0             	mov    %rsi,%rax
    c209:	48 89 74 24 48       	mov    %rsi,0x48(%rsp)
    c20e:	48 c1 e8 03          	shr    $0x3,%rax
    c212:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    c219:	48 89 f0             	mov    %rsi,%rax
    c21c:	83 e0 07             	and    $0x7,%eax
    c21f:	83 c0 03             	add    $0x3,%eax
    c222:	38 d0                	cmp    %dl,%al
    c224:	7c 08                	jl     c22e <io_thread+0x4ce>
    c226:	84 d2                	test   %dl,%dl
    c228:	0f 85 33 13 00 00    	jne    d561 <io_thread+0x1801>
	if (ring->flags & IORING_SETUP_SQE128)
    c22e:	48 8d b3 00 fb ff ff 	lea    -0x500(%rbx),%rsi
	unsigned int head, next = sq->sqe_tail + 1;
    c235:	8b 83 84 fa ff ff    	mov    -0x57c(%rbx),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    c23b:	48 89 f2             	mov    %rsi,%rdx
    c23e:	48 89 74 24 10       	mov    %rsi,0x10(%rsp)
    c243:	48 c1 ea 03          	shr    $0x3,%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    c247:	83 c0 01             	add    $0x1,%eax
	if (ring->flags & IORING_SETUP_SQE128)
    c24a:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    c251:	84 d2                	test   %dl,%dl
    c253:	74 09                	je     c25e <io_thread+0x4fe>
    c255:	80 fa 03             	cmp    $0x3,%dl
    c258:	0f 8e 79 13 00 00    	jle    d5d7 <io_thread+0x1877>
    c25e:	8b 8b 00 fb ff ff    	mov    -0x500(%rbx),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    c264:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    c269:	89 ca                	mov    %ecx,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    c26b:	48 c1 ee 03          	shr    $0x3,%rsi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    c26f:	83 e2 02             	and    $0x2,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    c272:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    c279:	0f 85 4e 13 00 00    	jne    d5cd <io_thread+0x186d>
    c27f:	48 8b bb 40 fa ff ff 	mov    -0x5c0(%rbx),%rdi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    c286:	85 d2                	test   %edx,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    c288:	48 89 fa             	mov    %rdi,%rdx
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    c28b:	0f 85 3f 0b 00 00    	jne    cdd0 <io_thread+0x1070>
		head = IO_URING_READ_ONCE(*sq->khead);
    c291:	48 c1 ea 03          	shr    $0x3,%rdx
    c295:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    c29c:	48 89 fa             	mov    %rdi,%rdx
    c29f:	83 e2 07             	and    $0x7,%edx
    c2a2:	83 c2 03             	add    $0x3,%edx
    c2a5:	40 38 f2             	cmp    %sil,%dl
    c2a8:	7c 09                	jl     c2b3 <io_thread+0x553>
    c2aa:	40 84 f6             	test   %sil,%sil
    c2ad:	0f 85 85 12 00 00    	jne    d538 <io_thread+0x17d8>
    c2b3:	8b 17                	mov    (%rdi),%edx
	if (next - head <= sq->ring_entries) {
    c2b5:	4c 8d 93 9c fa ff ff 	lea    -0x564(%rbx),%r10
    c2bc:	89 c7                	mov    %eax,%edi
    c2be:	29 d7                	sub    %edx,%edi
    c2c0:	4c 89 d2             	mov    %r10,%rdx
    c2c3:	4c 89 54 24 50       	mov    %r10,0x50(%rsp)
    c2c8:	48 c1 ea 03          	shr    $0x3,%rdx
    c2cc:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    c2d3:	4c 89 d2             	mov    %r10,%rdx
    c2d6:	83 e2 07             	and    $0x7,%edx
    c2d9:	83 c2 03             	add    $0x3,%edx
    c2dc:	40 38 f2             	cmp    %sil,%dl
    c2df:	7c 09                	jl     c2ea <io_thread+0x58a>
    c2e1:	40 84 f6             	test   %sil,%sil
    c2e4:	0f 85 53 12 00 00    	jne    d53d <io_thread+0x17dd>
    c2ea:	39 bb 9c fa ff ff    	cmp    %edi,-0x564(%rbx)
    c2f0:	0f 82 3f 87 ff ff    	jb     4a35 <io_thread.cold+0x63>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    c2f6:	48 8d b3 78 fa ff ff 	lea    -0x588(%rbx),%rsi
    c2fd:	48 89 f2             	mov    %rsi,%rdx
    c300:	48 89 74 24 70       	mov    %rsi,0x70(%rsp)
    c305:	48 c1 ea 03          	shr    $0x3,%rdx
    c309:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    c310:	0f 85 2f 12 00 00    	jne    d545 <io_thread+0x17e5>
    c316:	48 8d b3 98 fa ff ff 	lea    -0x568(%rbx),%rsi
    c31d:	48 8b bb 78 fa ff ff 	mov    -0x588(%rbx),%rdi
    c324:	8b 93 84 fa ff ff    	mov    -0x57c(%rbx),%edx
    c32a:	48 89 74 24 78       	mov    %rsi,0x78(%rsp)
    c32f:	48 c1 ee 03          	shr    $0x3,%rsi
    c333:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    c33a:	40 84 f6             	test   %sil,%sil
    c33d:	74 0a                	je     c349 <io_thread+0x5e9>
    c33f:	40 80 fe 03          	cmp    $0x3,%sil
    c343:	0f 8e 04 12 00 00    	jle    d54d <io_thread+0x17ed>
		sq->sqe_tail = next;
    c349:	89 83 84 fa ff ff    	mov    %eax,-0x57c(%rbx)
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    c34f:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
	if (ring->flags & IORING_SETUP_SQE128)
    c354:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    c357:	23 93 98 fa ff ff    	and    -0x568(%rbx),%edx
	if (ring->flags & IORING_SETUP_SQE128)
    c35d:	83 e1 01             	and    $0x1,%ecx
    c360:	48 83 c0 60          	add    $0x60,%rax
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    c364:	d3 e2                	shl    %cl,%edx
    c366:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    c36b:	48 c1 e8 03          	shr    $0x3,%rax
    c36f:	48 c1 e2 06          	shl    $0x6,%rdx
    c373:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    c37a:	48 01 d7             	add    %rdx,%rdi
    c37d:	84 c0                	test   %al,%al
    c37f:	74 08                	je     c389 <io_thread+0x629>
    c381:	3c 03                	cmp    $0x3,%al
    c383:	0f 8e ce 11 00 00    	jle    d557 <io_thread+0x17f7>
    c389:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    c38e:	8b 70 60             	mov    0x60(%rax),%esi
	sqe->opcode = (__u8) op;
    c391:	48 89 f8             	mov    %rdi,%rax
    c394:	48 c1 e8 03          	shr    $0x3,%rax
    c398:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    c39f:	84 c0                	test   %al,%al
    c3a1:	74 06                	je     c3a9 <io_thread+0x649>
    c3a3:	0f 8e 6a 12 00 00    	jle    d613 <io_thread+0x18b3>
	sqe->flags = 0;
    c3a9:	48 8d 47 01          	lea    0x1(%rdi),%rax
	sqe->opcode = (__u8) op;
    c3ad:	c6 07 01             	movb   $0x1,(%rdi)
	sqe->flags = 0;
    c3b0:	48 89 c2             	mov    %rax,%rdx
    c3b3:	48 89 c1             	mov    %rax,%rcx
    c3b6:	48 c1 ea 03          	shr    $0x3,%rdx
    c3ba:	83 e1 07             	and    $0x7,%ecx
    c3bd:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    c3c4:	38 ca                	cmp    %cl,%dl
    c3c6:	7f 08                	jg     c3d0 <io_thread+0x670>
    c3c8:	84 d2                	test   %dl,%dl
    c3ca:	0f 85 48 12 00 00    	jne    d618 <io_thread+0x18b8>
	sqe->ioprio = 0;
    c3d0:	48 8d 57 02          	lea    0x2(%rdi),%rdx
	sqe->flags = 0;
    c3d4:	c6 47 01 00          	movb   $0x0,0x1(%rdi)
	sqe->ioprio = 0;
    c3d8:	48 89 d0             	mov    %rdx,%rax
    c3db:	48 c1 e8 03          	shr    $0x3,%rax
    c3df:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    c3e6:	48 89 d0             	mov    %rdx,%rax
    c3e9:	83 e0 07             	and    $0x7,%eax
    c3ec:	83 c0 01             	add    $0x1,%eax
    c3ef:	38 c8                	cmp    %cl,%al
    c3f1:	7c 08                	jl     c3fb <io_thread+0x69b>
    c3f3:	84 c9                	test   %cl,%cl
    c3f5:	0f 85 25 12 00 00    	jne    d620 <io_thread+0x18c0>
	sqe->fd = fd;
    c3fb:	48 8d 57 04          	lea    0x4(%rdi),%rdx
	sqe->ioprio = 0;
    c3ff:	45 31 db             	xor    %r11d,%r11d
	sqe->fd = fd;
    c402:	48 89 d0             	mov    %rdx,%rax
	sqe->ioprio = 0;
    c405:	66 44 89 5f 02       	mov    %r11w,0x2(%rdi)
	sqe->fd = fd;
    c40a:	48 c1 e8 03          	shr    $0x3,%rax
    c40e:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    c415:	48 89 d0             	mov    %rdx,%rax
    c418:	83 e0 07             	and    $0x7,%eax
    c41b:	83 c0 03             	add    $0x3,%eax
    c41e:	38 c8                	cmp    %cl,%al
    c420:	7c 08                	jl     c42a <io_thread+0x6ca>
    c422:	84 c9                	test   %cl,%cl
    c424:	0f 85 fe 11 00 00    	jne    d628 <io_thread+0x18c8>
	sqe->off = offset;
    c42a:	48 8d 47 08          	lea    0x8(%rdi),%rax
	sqe->fd = fd;
    c42e:	89 77 04             	mov    %esi,0x4(%rdi)
	sqe->off = offset;
    c431:	48 89 c2             	mov    %rax,%rdx
    c434:	48 c1 ea 03          	shr    $0x3,%rdx
    c438:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    c43f:	0f 85 eb 11 00 00    	jne    d630 <io_thread+0x18d0>
	sqe->addr = (unsigned long) addr;
    c445:	48 8d 47 10          	lea    0x10(%rdi),%rax
	sqe->off = offset;
    c449:	48 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%rdi)
	sqe->addr = (unsigned long) addr;
    c451:	48 89 c2             	mov    %rax,%rdx
    c454:	48 c1 ea 03          	shr    $0x3,%rdx
    c458:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    c45f:	0f 85 d3 11 00 00    	jne    d638 <io_thread+0x18d8>
    c465:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
	sqe->len = len;
    c46a:	48 8d 57 18          	lea    0x18(%rdi),%rdx
	sqe->addr = (unsigned long) addr;
    c46e:	48 89 47 10          	mov    %rax,0x10(%rdi)
	sqe->len = len;
    c472:	48 89 d0             	mov    %rdx,%rax
    c475:	48 c1 e8 03          	shr    $0x3,%rax
    c479:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    c480:	84 c0                	test   %al,%al
    c482:	74 08                	je     c48c <io_thread+0x72c>
    c484:	3c 03                	cmp    $0x3,%al
    c486:	0f 8e b4 11 00 00    	jle    d640 <io_thread+0x18e0>
	sqe->rw_flags = 0;
    c48c:	48 8d 57 1c          	lea    0x1c(%rdi),%rdx
	sqe->len = len;
    c490:	c7 47 18 01 00 00 00 	movl   $0x1,0x18(%rdi)
	sqe->rw_flags = 0;
    c497:	48 89 d0             	mov    %rdx,%rax
    c49a:	48 c1 e8 03          	shr    $0x3,%rax
    c49e:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    c4a5:	48 89 d0             	mov    %rdx,%rax
    c4a8:	83 e0 07             	and    $0x7,%eax
    c4ab:	83 c0 03             	add    $0x3,%eax
    c4ae:	38 c8                	cmp    %cl,%al
    c4b0:	7c 08                	jl     c4ba <io_thread+0x75a>
    c4b2:	84 c9                	test   %cl,%cl
    c4b4:	0f 85 8e 11 00 00    	jne    d648 <io_thread+0x18e8>
	sqe->buf_index = 0;
    c4ba:	48 8d 57 28          	lea    0x28(%rdi),%rdx
	sqe->rw_flags = 0;
    c4be:	c7 47 1c 00 00 00 00 	movl   $0x0,0x1c(%rdi)
	sqe->buf_index = 0;
    c4c5:	48 89 d0             	mov    %rdx,%rax
    c4c8:	48 c1 e8 03          	shr    $0x3,%rax
    c4cc:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    c4d3:	84 c0                	test   %al,%al
    c4d5:	74 08                	je     c4df <io_thread+0x77f>
    c4d7:	3c 01                	cmp    $0x1,%al
    c4d9:	0f 8e 71 11 00 00    	jle    d650 <io_thread+0x18f0>
	sqe->personality = 0;
    c4df:	48 8d 57 2a          	lea    0x2a(%rdi),%rdx
	sqe->buf_index = 0;
    c4e3:	45 31 d2             	xor    %r10d,%r10d
	sqe->personality = 0;
    c4e6:	48 89 d0             	mov    %rdx,%rax
	sqe->buf_index = 0;
    c4e9:	66 44 89 57 28       	mov    %r10w,0x28(%rdi)
	sqe->personality = 0;
    c4ee:	48 c1 e8 03          	shr    $0x3,%rax
    c4f2:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    c4f9:	48 89 d0             	mov    %rdx,%rax
    c4fc:	83 e0 07             	and    $0x7,%eax
    c4ff:	83 c0 01             	add    $0x1,%eax
    c502:	38 c8                	cmp    %cl,%al
    c504:	7c 08                	jl     c50e <io_thread+0x7ae>
    c506:	84 c9                	test   %cl,%cl
    c508:	0f 85 4a 11 00 00    	jne    d658 <io_thread+0x18f8>
	sqe->file_index = 0;
    c50e:	48 8d 57 2c          	lea    0x2c(%rdi),%rdx
	sqe->personality = 0;
    c512:	45 31 c9             	xor    %r9d,%r9d
	sqe->file_index = 0;
    c515:	48 89 d0             	mov    %rdx,%rax
	sqe->personality = 0;
    c518:	66 44 89 4f 2a       	mov    %r9w,0x2a(%rdi)
	sqe->file_index = 0;
    c51d:	48 c1 e8 03          	shr    $0x3,%rax
    c521:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    c528:	48 89 d0             	mov    %rdx,%rax
    c52b:	83 e0 07             	and    $0x7,%eax
    c52e:	83 c0 03             	add    $0x3,%eax
    c531:	38 c8                	cmp    %cl,%al
    c533:	7c 08                	jl     c53d <io_thread+0x7dd>
    c535:	84 c9                	test   %cl,%cl
    c537:	0f 85 23 11 00 00    	jne    d660 <io_thread+0x1900>
	sqe->addr3 = 0;
    c53d:	48 8d 47 30          	lea    0x30(%rdi),%rax
	sqe->file_index = 0;
    c541:	c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%rdi)
	sqe->addr3 = 0;
    c548:	48 89 c2             	mov    %rax,%rdx
    c54b:	48 c1 ea 03          	shr    $0x3,%rdx
    c54f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    c556:	0f 85 0c 11 00 00    	jne    d668 <io_thread+0x1908>
	sqe->__pad2[0] = 0;
    c55c:	48 8d 47 38          	lea    0x38(%rdi),%rax
	sqe->addr3 = 0;
    c560:	48 c7 47 30 00 00 00 00 	movq   $0x0,0x30(%rdi)
	sqe->__pad2[0] = 0;
    c568:	48 89 c2             	mov    %rax,%rdx
    c56b:	48 c1 ea 03          	shr    $0x3,%rdx
    c56f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    c576:	0f 85 51 0f 00 00    	jne    d4cd <io_thread+0x176d>
	sqe->user_data = (unsigned long) data;
    c57c:	48 8d 47 20          	lea    0x20(%rdi),%rax
	sqe->__pad2[0] = 0;
    c580:	48 c7 47 38 00 00 00 00 	movq   $0x0,0x38(%rdi)
	sqe->user_data = (unsigned long) data;
    c588:	48 89 c2             	mov    %rax,%rdx
    c58b:	48 c1 ea 03          	shr    $0x3,%rdx
    c58f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    c596:	0f 85 39 0f 00 00    	jne    d4d5 <io_thread+0x1775>
    c59c:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    c5a1:	48 89 47 20          	mov    %rax,0x20(%rdi)
  io_uring_submit(&ring);
    c5a5:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    c5aa:	e8 b1 80 ff ff       	call   4660 <io_uring_submit@plt>
  while (data->running == 1) {
    c5af:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    c5b4:	48 8d 70 44          	lea    0x44(%rax),%rsi
    c5b8:	48 89 f0             	mov    %rsi,%rax
    c5bb:	48 89 74 24 68       	mov    %rsi,0x68(%rsp)
    c5c0:	48 c1 e8 03          	shr    $0x3,%rax
    c5c4:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    c5cb:	48 89 f0             	mov    %rsi,%rax
    c5ce:	83 e0 07             	and    $0x7,%eax
    c5d1:	83 c0 03             	add    $0x3,%eax
    c5d4:	38 d0                	cmp    %dl,%al
    c5d6:	7c 08                	jl     c5e0 <io_thread+0x880>
    c5d8:	84 d2                	test   %dl,%dl
    c5da:	0f 85 2b 10 00 00    	jne    d60b <io_thread+0x18ab>
    c5e0:	48 8d 83 f0 fa ff ff 	lea    -0x510(%rbx),%rax
    c5e7:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
		unsigned head = *ring->cq.khead;
    c5ec:	48 8d 83 a8 fa ff ff 	lea    -0x558(%rbx),%rax
    c5f3:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    c5f8:	48 c1 e8 03          	shr    $0x3,%rax
    c5fc:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    c601:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    c606:	83 78 44 01          	cmpl   $0x1,0x44(%rax)
    c60a:	0f 85 20 07 00 00    	jne    cd30 <io_thread+0xfd0>
    c610:	48 89 ac 24 a8 00 00 00 	mov    %rbp,0xa8(%rsp)
    c618:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    c620:	48 8d 3d f9 55 00 00 	lea    0x55f9(%rip),%rdi        # 11c20 <_IO_stdin_used+0xc20>
    c627:	e8 d4 81 ff ff       	call   4800 <puts@plt>
	unsigned mask = ring->cq.ring_mask;
    c62c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    c631:	48 c1 e8 03          	shr    $0x3,%rax
    c635:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    c63c:	84 c0                	test   %al,%al
    c63e:	74 08                	je     c648 <io_thread+0x8e8>
    c640:	3c 03                	cmp    $0x3,%al
    c642:	0f 8e 41 0d 00 00    	jle    d389 <io_thread+0x1629>
	if (ring->flags & IORING_SETUP_CQE32)
    c648:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
	unsigned mask = ring->cq.ring_mask;
    c64d:	44 8b bb f0 fa ff ff 	mov    -0x510(%rbx),%r15d
	if (ring->flags & IORING_SETUP_CQE32)
    c654:	48 c1 e8 03          	shr    $0x3,%rax
    c658:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    c65f:	84 c0                	test   %al,%al
    c661:	74 08                	je     c66b <io_thread+0x90b>
    c663:	3c 03                	cmp    $0x3,%al
    c665:	0f 8e 95 0c 00 00    	jle    d300 <io_thread+0x15a0>
    c66b:	8b 8b 00 fb ff ff    	mov    -0x500(%rbx),%ecx
    c671:	4c 8d b3 b0 fa ff ff 	lea    -0x550(%rbx),%r14
		cqe = &ring->cq.cqes[(head & mask) << shift];
    c678:	4c 8d ab d8 fa ff ff 	lea    -0x528(%rbx),%r13
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    c67f:	48 8d b3 08 fb ff ff 	lea    -0x4f8(%rbx),%rsi
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    c686:	4d 89 f2             	mov    %r14,%r10
		cqe = &ring->cq.cqes[(head & mask) << shift];
    c689:	4d 89 ec             	mov    %r13,%r12
	if (ring->flags & IORING_SETUP_CQE32)
    c68c:	c1 e9 0b             	shr    $0xb,%ecx
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    c68f:	49 89 f3             	mov    %rsi,%r11
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    c692:	49 c1 ea 03          	shr    $0x3,%r10
		cqe = &ring->cq.cqes[(head & mask) << shift];
    c696:	49 c1 ec 03          	shr    $0x3,%r12
	if (ring->flags & IORING_SETUP_CQE32)
    c69a:	83 e1 01             	and    $0x1,%ecx
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    c69d:	49 c1 eb 03          	shr    $0x3,%r11
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    c6a1:	41 80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r10)
    c6a9:	0f 85 1a 0c 00 00    	jne    d2c9 <io_thread+0x1569>
    c6af:	48 8b bb b0 fa ff ff 	mov    -0x550(%rbx),%rdi
    c6b6:	48 89 f8             	mov    %rdi,%rax
    c6b9:	48 c1 e8 03          	shr    $0x3,%rax
    c6bd:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    c6c4:	48 89 f8             	mov    %rdi,%rax
    c6c7:	83 e0 07             	and    $0x7,%eax
    c6ca:	83 c0 03             	add    $0x3,%eax
    c6cd:	38 d0                	cmp    %dl,%al
    c6cf:	7c 08                	jl     c6d9 <io_thread+0x979>
    c6d1:	84 d2                	test   %dl,%dl
    c6d3:	0f 85 f8 0b 00 00    	jne    d2d1 <io_thread+0x1571>
    c6d9:	44 8b 07             	mov    (%rdi),%r8d
		unsigned head = *ring->cq.khead;
    c6dc:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    c6e1:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c6e8:	0f 85 e8 0b 00 00    	jne    d2d6 <io_thread+0x1576>
    c6ee:	48 8b 93 a8 fa ff ff 	mov    -0x558(%rbx),%rdx
    c6f5:	48 89 d0             	mov    %rdx,%rax
    c6f8:	48 c1 e8 03          	shr    $0x3,%rax
    c6fc:	0f b6 b8 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edi
    c703:	48 89 d0             	mov    %rdx,%rax
    c706:	83 e0 07             	and    $0x7,%eax
    c709:	83 c0 03             	add    $0x3,%eax
    c70c:	40 38 f8             	cmp    %dil,%al
    c70f:	7c 09                	jl     c71a <io_thread+0x9ba>
    c711:	40 84 ff             	test   %dil,%dil
    c714:	0f 85 c6 0b 00 00    	jne    d2e0 <io_thread+0x1580>
    c71a:	8b 02                	mov    (%rdx),%eax
		if (!available)
    c71c:	41 39 c0             	cmp    %eax,%r8d
    c71f:	0f 84 96 00 00 00    	je     c7bb <io_thread+0xa5b>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    c725:	41 80 bc 24 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r12)
    c72e:	0f 85 b4 0b 00 00    	jne    d2e8 <io_thread+0x1588>
    c734:	44 89 ff             	mov    %r15d,%edi
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    c737:	45 0f b6 83 00 80 ff 7f 	movzbl 0x7fff8000(%r11),%r8d
		cqe = &ring->cq.cqes[(head & mask) << shift];
    c73f:	21 c7                	and    %eax,%edi
    c741:	d3 e7                	shl    %cl,%edi
    c743:	48 c1 e7 04          	shl    $0x4,%rdi
    c747:	48 03 bb d8 fa ff ff 	add    -0x528(%rbx),%rdi
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    c74e:	45 84 c0             	test   %r8b,%r8b
    c751:	74 0a                	je     c75d <io_thread+0x9fd>
    c753:	41 80 f8 03          	cmp    $0x3,%r8b
    c757:	0f 8e 93 0b 00 00    	jle    d2f0 <io_thread+0x1590>
    c75d:	f6 83 09 fb ff ff 01 	testb  $0x1,-0x4f7(%rbx)
    c764:	0f 85 96 06 00 00    	jne    ce00 <io_thread+0x10a0>
				cqe->user_data == LIBURING_UDATA_TIMEOUT) {
    c76a:	49 89 f8             	mov    %rdi,%r8
    c76d:	49 c1 e8 03          	shr    $0x3,%r8
    c771:	41 80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r8)
    c779:	0f 85 3d 0b 00 00    	jne    d2bc <io_thread+0x155c>
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    c77f:	48 83 3f ff          	cmpq   $0xffffffffffffffff,(%rdi)
    c783:	0f 85 77 0a 00 00    	jne    d200 <io_thread+0x14a0>
			if (cqe->res < 0)
    c789:	4c 8d 47 08          	lea    0x8(%rdi),%r8
    c78d:	4d 89 c1             	mov    %r8,%r9
    c790:	49 c1 e9 03          	shr    $0x3,%r9
    c794:	45 0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%r9),%r9d
    c79c:	45 84 c9             	test   %r9b,%r9b
    c79f:	74 0a                	je     c7ab <io_thread+0xa4b>
    c7a1:	41 80 f9 03          	cmp    $0x3,%r9b
    c7a5:	0f 8e 16 0b 00 00    	jle    d2c1 <io_thread+0x1561>
    c7ab:	8b 7f 08             	mov    0x8(%rdi),%edi
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    c7ae:	83 c0 01             	add    $0x1,%eax
    c7b1:	89 02                	mov    %eax,(%rdx)
			if (!err)
    c7b3:	85 ff                	test   %edi,%edi
    c7b5:	0f 89 e6 fe ff ff    	jns    c6a1 <io_thread+0x941>
	*cqe_ptr = cqe;
    c7bb:	4c 8d bb e0 f9 ff ff 	lea    -0x620(%rbx),%r15
    c7c2:	4c 89 f8             	mov    %r15,%rax
    c7c5:	48 c1 e8 03          	shr    $0x3,%rax
    c7c9:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c7d0:	0f 85 09 0e 00 00    	jne    d5df <io_thread+0x187f>
    c7d6:	48 c7 83 e0 f9 ff ff 00 00 00 00 	movq   $0x0,-0x620(%rbx)
	return err;
    c7e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    c7e8:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
      if (cqe->user_data == 1) {
    c7ed:	4d 89 fc             	mov    %r15,%r12
    c7f0:	45 31 c0             	xor    %r8d,%r8d
    c7f3:	31 d2                	xor    %edx,%edx
    c7f5:	b9 01 00 00 00       	mov    $0x1,%ecx
    c7fa:	4c 89 fe             	mov    %r15,%rsi
    c7fd:	49 c1 ec 03          	shr    $0x3,%r12
    c801:	e8 3a 7f ff ff       	call   4740 <__io_uring_get_cqe@plt>
    c806:	41 80 bc 24 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r12)
    c80f:	41 89 c5             	mov    %eax,%r13d
    c812:	0f 85 01 0c 00 00    	jne    d419 <io_thread+0x16b9>
    c818:	48 8b bb e0 f9 ff ff 	mov    -0x620(%rbx),%rdi
    c81f:	48 89 f8             	mov    %rdi,%rax
    c822:	48 c1 e8 03          	shr    $0x3,%rax
    c826:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c82d:	0f 85 ee 0b 00 00    	jne    d421 <io_thread+0x16c1>
    c833:	48 83 3f 01          	cmpq   $0x1,(%rdi)
    c837:	0f 84 f3 09 00 00    	je     d230 <io_thread+0x14d0>
    c83d:	48 8d 3d 5c 54 00 00 	lea    0x545c(%rip),%rdi        # 11ca0 <_IO_stdin_used+0xca0>
    c844:	e8 b7 7f ff ff       	call   4800 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    c849:	41 80 bc 24 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r12)
    c852:	0f 85 ce 0b 00 00    	jne    d426 <io_thread+0x16c6>
    c858:	48 8b bb e0 f9 ff ff 	mov    -0x620(%rbx),%rdi
    c85f:	48 89 f8             	mov    %rdi,%rax
    c862:	48 c1 e8 03          	shr    $0x3,%rax
    c866:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c86d:	0f 85 bb 0b 00 00    	jne    d42e <io_thread+0x16ce>
    c873:	4c 8b 37             	mov    (%rdi),%r14
      if (ret < 0)
    c876:	45 85 ed             	test   %r13d,%r13d
    c879:	0f 88 94 81 ff ff    	js     4a13 <io_thread.cold+0x41>
      if (cqe->res < 0) {
    c87f:	48 8d 57 08          	lea    0x8(%rdi),%rdx
    c883:	48 89 d0             	mov    %rdx,%rax
    c886:	48 c1 e8 03          	shr    $0x3,%rax
    c88a:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    c891:	84 c0                	test   %al,%al
    c893:	74 08                	je     c89d <io_thread+0xb3d>
    c895:	3c 03                	cmp    $0x3,%al
    c897:	0f 8e f6 0a 00 00    	jle    d393 <io_thread+0x1633>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    c89d:	4c 89 f2             	mov    %r14,%rdx
      if (cqe->res < 0) {
    c8a0:	8b 47 08             	mov    0x8(%rdi),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    c8a3:	48 c1 ea 03          	shr    $0x3,%rdx
    c8a7:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    c8ae:	84 d2                	test   %dl,%dl
    c8b0:	74 09                	je     c8bb <io_thread+0xb5b>
    c8b2:	80 fa 03             	cmp    $0x3,%dl
    c8b5:	0f 8e 57 0a 00 00    	jle    d312 <io_thread+0x15b2>
    c8bb:	45 8b 26             	mov    (%r14),%r12d
      if (cqe->res < 0) {
    c8be:	85 c0                	test   %eax,%eax
    c8c0:	0f 88 54 0a 00 00    	js     d31a <io_thread+0x15ba>
      switch (req->event_type) {
    c8c6:	41 83 fc 01          	cmp    $0x1,%r12d
    c8ca:	0f 84 38 07 00 00    	je     d008 <io_thread+0x12a8>
    c8d0:	41 83 fc 02          	cmp    $0x2,%r12d
    c8d4:	0f 84 36 06 00 00    	je     cf10 <io_thread+0x11b0>
    c8da:	45 85 e4             	test   %r12d,%r12d
    c8dd:	0f 85 ad 05 00 00    	jne    ce90 <io_thread+0x1130>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    c8e3:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    c8e8:	48 8b 94 24 80 00 00 00 	mov    0x80(%rsp),%rdx
    c8f0:	48 8b b4 24 90 00 00 00 	mov    0x90(%rsp),%rsi
    c8f8:	8b 7c 24 44          	mov    0x44(%rsp),%edi
    c8fc:	e8 2f f0 ff ff       	call   b930 <add_accept_request>
              add_read_request(cqe->res, &ring);
    c901:	4c 89 f8             	mov    %r15,%rax
    c904:	48 c1 e8 03          	shr    $0x3,%rax
    c908:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c90f:	0f 85 96 0a 00 00    	jne    d3ab <io_thread+0x164b>
    c915:	48 8b 83 e0 f9 ff ff 	mov    -0x620(%rbx),%rax
    c91c:	48 8d 78 08          	lea    0x8(%rax),%rdi
    c920:	48 89 fa             	mov    %rdi,%rdx
    c923:	48 c1 ea 03          	shr    $0x3,%rdx
    c927:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    c92e:	84 d2                	test   %dl,%dl
    c930:	74 09                	je     c93b <io_thread+0xbdb>
    c932:	80 fa 03             	cmp    $0x3,%dl
    c935:	0f 8e 78 0a 00 00    	jle    d3b3 <io_thread+0x1653>
    c93b:	8b 78 08             	mov    0x8(%rax),%edi
    c93e:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    c943:	e8 48 db ff ff       	call   a490 <add_read_request>
              free(req);
    c948:	4c 89 f7             	mov    %r14,%rdi
    c94b:	e8 50 7e ff ff       	call   47a0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    c950:	4c 89 f8             	mov    %r15,%rax
    c953:	48 c1 e8 03          	shr    $0x3,%rax
    c957:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    c95e:	0f 85 61 0a 00 00    	jne    d3c5 <io_thread+0x1665>
    c964:	48 8b 83 e0 f9 ff ff 	mov    -0x620(%rbx),%rax
	if (cqe)
    c96b:	48 85 c0             	test   %rax,%rax
    c96e:	0f 85 1c 05 00 00    	jne    ce90 <io_thread+0x1130>
	unsigned int head, next = sq->sqe_tail + 1;
    c974:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
    c979:	48 89 f0             	mov    %rsi,%rax
    c97c:	48 c1 e8 03          	shr    $0x3,%rax
    c980:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    c987:	48 89 f0             	mov    %rsi,%rax
    c98a:	83 e0 07             	and    $0x7,%eax
    c98d:	83 c0 03             	add    $0x3,%eax
    c990:	38 d0                	cmp    %dl,%al
    c992:	7c 08                	jl     c99c <io_thread+0xc3c>
    c994:	84 d2                	test   %dl,%dl
    c996:	0f 85 d1 09 00 00    	jne    d36d <io_thread+0x160d>
	if (ring->flags & IORING_SETUP_SQE128)
    c99c:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    c9a1:	8b 83 84 fa ff ff    	mov    -0x57c(%rbx),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    c9a7:	48 c1 ea 03          	shr    $0x3,%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    c9ab:	83 c0 01             	add    $0x1,%eax
	if (ring->flags & IORING_SETUP_SQE128)
    c9ae:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    c9b5:	84 d2                	test   %dl,%dl
    c9b7:	74 09                	je     c9c2 <io_thread+0xc62>
    c9b9:	80 fa 03             	cmp    $0x3,%dl
    c9bc:	0f 8e b3 09 00 00    	jle    d375 <io_thread+0x1615>
    c9c2:	8b 8b 00 fb ff ff    	mov    -0x500(%rbx),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    c9c8:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    c9cd:	89 ca                	mov    %ecx,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    c9cf:	48 c1 ee 03          	shr    $0x3,%rsi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    c9d3:	83 e2 02             	and    $0x2,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    c9d6:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    c9dd:	0f 85 9c 09 00 00    	jne    d37f <io_thread+0x161f>
    c9e3:	48 8b bb 40 fa ff ff 	mov    -0x5c0(%rbx),%rdi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    c9ea:	85 d2                	test   %edx,%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    c9ec:	48 89 fa             	mov    %rdi,%rdx
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    c9ef:	0f 85 eb 04 00 00    	jne    cee0 <io_thread+0x1180>
		head = IO_URING_READ_ONCE(*sq->khead);
    c9f5:	48 c1 ea 03          	shr    $0x3,%rdx
    c9f9:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    ca00:	48 89 fa             	mov    %rdi,%rdx
    ca03:	83 e2 07             	and    $0x7,%edx
    ca06:	83 c2 03             	add    $0x3,%edx
    ca09:	40 38 f2             	cmp    %sil,%dl
    ca0c:	7c 09                	jl     ca17 <io_thread+0xcb7>
    ca0e:	40 84 f6             	test   %sil,%sil
    ca11:	0f 85 79 08 00 00    	jne    d290 <io_thread+0x1530>
    ca17:	8b 17                	mov    (%rdi),%edx
	if (next - head <= sq->ring_entries) {
    ca19:	4c 8b 5c 24 50       	mov    0x50(%rsp),%r11
    ca1e:	89 c7                	mov    %eax,%edi
    ca20:	29 d7                	sub    %edx,%edi
    ca22:	4c 89 da             	mov    %r11,%rdx
    ca25:	48 c1 ea 03          	shr    $0x3,%rdx
    ca29:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    ca30:	4c 89 da             	mov    %r11,%rdx
    ca33:	83 e2 07             	and    $0x7,%edx
    ca36:	83 c2 03             	add    $0x3,%edx
    ca39:	40 38 f2             	cmp    %sil,%dl
    ca3c:	7c 09                	jl     ca47 <io_thread+0xce7>
    ca3e:	40 84 f6             	test   %sil,%sil
    ca41:	0f 85 b1 08 00 00    	jne    d2f8 <io_thread+0x1598>
    ca47:	39 bb 9c fa ff ff    	cmp    %edi,-0x564(%rbx)
    ca4d:	0f 82 7f 7f ff ff    	jb     49d2 <io_thread.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    ca53:	48 8b 54 24 70       	mov    0x70(%rsp),%rdx
    ca58:	48 c1 ea 03          	shr    $0x3,%rdx
    ca5c:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    ca63:	0f 85 a6 09 00 00    	jne    d40f <io_thread+0x16af>
    ca69:	48 8b 74 24 78       	mov    0x78(%rsp),%rsi
    ca6e:	48 8b 93 78 fa ff ff 	mov    -0x588(%rbx),%rdx
    ca75:	8b bb 84 fa ff ff    	mov    -0x57c(%rbx),%edi
    ca7b:	48 c1 ee 03          	shr    $0x3,%rsi
    ca7f:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    ca86:	40 84 f6             	test   %sil,%sil
    ca89:	74 0a                	je     ca95 <io_thread+0xd35>
    ca8b:	40 80 fe 03          	cmp    $0x3,%sil
    ca8f:	0f 8e 59 09 00 00    	jle    d3ee <io_thread+0x168e>
		sq->sqe_tail = next;
    ca95:	89 83 84 fa ff ff    	mov    %eax,-0x57c(%rbx)
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    ca9b:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
	if (ring->flags & IORING_SETUP_SQE128)
    caa0:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    caa3:	23 bb 98 fa ff ff    	and    -0x568(%rbx),%edi
	if (ring->flags & IORING_SETUP_SQE128)
    caa9:	83 e1 01             	and    $0x1,%ecx
    caac:	48 c1 e8 03          	shr    $0x3,%rax
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    cab0:	d3 e7                	shl    %cl,%edi
    cab2:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    cab9:	48 c1 e7 06          	shl    $0x6,%rdi
    cabd:	48 01 d7             	add    %rdx,%rdi
    cac0:	84 c0                	test   %al,%al
    cac2:	74 08                	je     cacc <io_thread+0xd6c>
    cac4:	3c 03                	cmp    $0x3,%al
    cac6:	0f 8e 2c 09 00 00    	jle    d3f8 <io_thread+0x1698>
    cacc:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    cad1:	8b 48 60             	mov    0x60(%rax),%ecx
	sqe->opcode = (__u8) op;
    cad4:	48 89 f8             	mov    %rdi,%rax
    cad7:	48 c1 e8 03          	shr    $0x3,%rax
    cadb:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    cae2:	84 c0                	test   %al,%al
    cae4:	74 06                	je     caec <io_thread+0xd8c>
    cae6:	0f 8e 16 09 00 00    	jle    d402 <io_thread+0x16a2>
	sqe->flags = 0;
    caec:	48 8d 47 01          	lea    0x1(%rdi),%rax
	sqe->opcode = (__u8) op;
    caf0:	c6 07 01             	movb   $0x1,(%rdi)
	sqe->flags = 0;
    caf3:	48 89 c2             	mov    %rax,%rdx
    caf6:	48 89 c6             	mov    %rax,%rsi
    caf9:	48 c1 ea 03          	shr    $0x3,%rdx
    cafd:	83 e6 07             	and    $0x7,%esi
    cb00:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    cb07:	40 38 f2             	cmp    %sil,%dl
    cb0a:	7f 08                	jg     cb14 <io_thread+0xdb4>
    cb0c:	84 d2                	test   %dl,%dl
    cb0e:	0f 85 f3 08 00 00    	jne    d407 <io_thread+0x16a7>
	sqe->ioprio = 0;
    cb14:	48 8d 57 02          	lea    0x2(%rdi),%rdx
	sqe->flags = 0;
    cb18:	c6 47 01 00          	movb   $0x0,0x1(%rdi)
	sqe->ioprio = 0;
    cb1c:	48 89 d0             	mov    %rdx,%rax
    cb1f:	48 c1 e8 03          	shr    $0x3,%rax
    cb23:	0f b6 b0 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%esi
    cb2a:	48 89 d0             	mov    %rdx,%rax
    cb2d:	83 e0 07             	and    $0x7,%eax
    cb30:	83 c0 01             	add    $0x1,%eax
    cb33:	40 38 f0             	cmp    %sil,%al
    cb36:	7c 09                	jl     cb41 <io_thread+0xde1>
    cb38:	40 84 f6             	test   %sil,%sil
    cb3b:	0f 85 f7 08 00 00    	jne    d438 <io_thread+0x16d8>
	sqe->fd = fd;
    cb41:	48 8d 57 04          	lea    0x4(%rdi),%rdx
	sqe->ioprio = 0;
    cb45:	31 f6                	xor    %esi,%esi
	sqe->fd = fd;
    cb47:	48 89 d0             	mov    %rdx,%rax
	sqe->ioprio = 0;
    cb4a:	66 89 77 02          	mov    %si,0x2(%rdi)
	sqe->fd = fd;
    cb4e:	48 c1 e8 03          	shr    $0x3,%rax
    cb52:	0f b6 b0 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%esi
    cb59:	48 89 d0             	mov    %rdx,%rax
    cb5c:	83 e0 07             	and    $0x7,%eax
    cb5f:	83 c0 03             	add    $0x3,%eax
    cb62:	40 38 f0             	cmp    %sil,%al
    cb65:	7c 09                	jl     cb70 <io_thread+0xe10>
    cb67:	40 84 f6             	test   %sil,%sil
    cb6a:	0f 85 d0 08 00 00    	jne    d440 <io_thread+0x16e0>
	sqe->off = offset;
    cb70:	48 8d 47 08          	lea    0x8(%rdi),%rax
	sqe->fd = fd;
    cb74:	89 4f 04             	mov    %ecx,0x4(%rdi)
	sqe->off = offset;
    cb77:	48 89 c2             	mov    %rax,%rdx
    cb7a:	48 c1 ea 03          	shr    $0x3,%rdx
    cb7e:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    cb85:	0f 85 bd 08 00 00    	jne    d448 <io_thread+0x16e8>
	sqe->addr = (unsigned long) addr;
    cb8b:	48 8d 47 10          	lea    0x10(%rdi),%rax
	sqe->off = offset;
    cb8f:	48 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%rdi)
	sqe->addr = (unsigned long) addr;
    cb97:	48 89 c2             	mov    %rax,%rdx
    cb9a:	48 c1 ea 03          	shr    $0x3,%rdx
    cb9e:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    cba5:	0f 85 a5 08 00 00    	jne    d450 <io_thread+0x16f0>
    cbab:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
	sqe->len = len;
    cbb0:	48 8d 57 18          	lea    0x18(%rdi),%rdx
	sqe->addr = (unsigned long) addr;
    cbb4:	48 89 47 10          	mov    %rax,0x10(%rdi)
	sqe->len = len;
    cbb8:	48 89 d0             	mov    %rdx,%rax
    cbbb:	48 c1 e8 03          	shr    $0x3,%rax
    cbbf:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    cbc6:	84 c0                	test   %al,%al
    cbc8:	74 08                	je     cbd2 <io_thread+0xe72>
    cbca:	3c 03                	cmp    $0x3,%al
    cbcc:	0f 8e 86 08 00 00    	jle    d458 <io_thread+0x16f8>
	sqe->rw_flags = 0;
    cbd2:	48 8d 57 1c          	lea    0x1c(%rdi),%rdx
	sqe->len = len;
    cbd6:	c7 47 18 01 00 00 00 	movl   $0x1,0x18(%rdi)
	sqe->rw_flags = 0;
    cbdd:	48 89 d0             	mov    %rdx,%rax
    cbe0:	48 c1 e8 03          	shr    $0x3,%rax
    cbe4:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    cbeb:	48 89 d0             	mov    %rdx,%rax
    cbee:	83 e0 07             	and    $0x7,%eax
    cbf1:	83 c0 03             	add    $0x3,%eax
    cbf4:	38 c8                	cmp    %cl,%al
    cbf6:	7c 08                	jl     cc00 <io_thread+0xea0>
    cbf8:	84 c9                	test   %cl,%cl
    cbfa:	0f 85 60 08 00 00    	jne    d460 <io_thread+0x1700>
	sqe->buf_index = 0;
    cc00:	48 8d 57 28          	lea    0x28(%rdi),%rdx
	sqe->rw_flags = 0;
    cc04:	c7 47 1c 00 00 00 00 	movl   $0x0,0x1c(%rdi)
	sqe->buf_index = 0;
    cc0b:	48 89 d0             	mov    %rdx,%rax
    cc0e:	48 c1 e8 03          	shr    $0x3,%rax
    cc12:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    cc19:	84 c0                	test   %al,%al
    cc1b:	74 08                	je     cc25 <io_thread+0xec5>
    cc1d:	3c 01                	cmp    $0x1,%al
    cc1f:	0f 8e 43 08 00 00    	jle    d468 <io_thread+0x1708>
    cc25:	31 d2                	xor    %edx,%edx
    cc27:	66 89 57 28          	mov    %dx,0x28(%rdi)
	sqe->personality = 0;
    cc2b:	48 8d 57 2a          	lea    0x2a(%rdi),%rdx
    cc2f:	48 89 d0             	mov    %rdx,%rax
    cc32:	48 c1 e8 03          	shr    $0x3,%rax
    cc36:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    cc3d:	48 89 d0             	mov    %rdx,%rax
    cc40:	83 e0 07             	and    $0x7,%eax
    cc43:	83 c0 01             	add    $0x1,%eax
    cc46:	38 c8                	cmp    %cl,%al
    cc48:	7c 08                	jl     cc52 <io_thread+0xef2>
    cc4a:	84 c9                	test   %cl,%cl
    cc4c:	0f 85 1e 08 00 00    	jne    d470 <io_thread+0x1710>
    cc52:	31 c0                	xor    %eax,%eax
	sqe->file_index = 0;
    cc54:	48 8d 57 2c          	lea    0x2c(%rdi),%rdx
	sqe->personality = 0;
    cc58:	66 89 47 2a          	mov    %ax,0x2a(%rdi)
	sqe->file_index = 0;
    cc5c:	48 89 d0             	mov    %rdx,%rax
    cc5f:	48 c1 e8 03          	shr    $0x3,%rax
    cc63:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    cc6a:	48 89 d0             	mov    %rdx,%rax
    cc6d:	83 e0 07             	and    $0x7,%eax
    cc70:	83 c0 03             	add    $0x3,%eax
    cc73:	38 c8                	cmp    %cl,%al
    cc75:	7c 08                	jl     cc7f <io_thread+0xf1f>
    cc77:	84 c9                	test   %cl,%cl
    cc79:	0f 85 f9 07 00 00    	jne    d478 <io_thread+0x1718>
	sqe->addr3 = 0;
    cc7f:	48 8d 47 30          	lea    0x30(%rdi),%rax
	sqe->file_index = 0;
    cc83:	c7 47 2c 00 00 00 00 	movl   $0x0,0x2c(%rdi)
	sqe->addr3 = 0;
    cc8a:	48 89 c2             	mov    %rax,%rdx
    cc8d:	48 c1 ea 03          	shr    $0x3,%rdx
    cc91:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    cc98:	0f 85 e2 07 00 00    	jne    d480 <io_thread+0x1720>
	sqe->__pad2[0] = 0;
    cc9e:	48 8d 47 38          	lea    0x38(%rdi),%rax
	sqe->addr3 = 0;
    cca2:	48 c7 47 30 00 00 00 00 	movq   $0x0,0x30(%rdi)
	sqe->__pad2[0] = 0;
    ccaa:	48 89 c2             	mov    %rax,%rdx
    ccad:	48 c1 ea 03          	shr    $0x3,%rdx
    ccb1:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    ccb8:	0f 85 ca 07 00 00    	jne    d488 <io_thread+0x1728>
	sqe->user_data = (unsigned long) data;
    ccbe:	48 8d 47 20          	lea    0x20(%rdi),%rax
	sqe->__pad2[0] = 0;
    ccc2:	48 c7 47 38 00 00 00 00 	movq   $0x0,0x38(%rdi)
	sqe->user_data = (unsigned long) data;
    ccca:	48 89 c2             	mov    %rax,%rdx
    cccd:	48 c1 ea 03          	shr    $0x3,%rdx
    ccd1:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    ccd8:	0f 85 bd 06 00 00    	jne    d39b <io_thread+0x163b>
    ccde:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    cce3:	48 89 47 20          	mov    %rax,0x20(%rdi)
      io_uring_submit(&ring);
    cce7:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    ccec:	e8 6f 79 ff ff       	call   4660 <io_uring_submit@plt>
  while (data->running == 1) {
    ccf1:	48 8b 74 24 68       	mov    0x68(%rsp),%rsi
    ccf6:	48 89 f0             	mov    %rsi,%rax
    ccf9:	48 c1 e8 03          	shr    $0x3,%rax
    ccfd:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    cd04:	48 89 f0             	mov    %rsi,%rax
    cd07:	83 e0 07             	and    $0x7,%eax
    cd0a:	83 c0 03             	add    $0x3,%eax
    cd0d:	38 d0                	cmp    %dl,%al
    cd0f:	7c 08                	jl     cd19 <io_thread+0xfb9>
    cd11:	84 d2                	test   %dl,%dl
    cd13:	0f 85 8a 06 00 00    	jne    d3a3 <io_thread+0x1643>
    cd19:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    cd1e:	83 78 44 01          	cmpl   $0x1,0x44(%rax)
    cd22:	0f 84 f8 f8 ff ff    	je     c620 <io_thread+0x8c0>
    cd28:	48 8b ac 24 a8 00 00 00 	mov    0xa8(%rsp),%rbp
    cd30:	48 8d 3d 89 50 00 00 	lea    0x5089(%rip),%rdi        # 11dc0 <_IO_stdin_used+0xdc0>
    cd37:	e8 c4 7a ff ff       	call   4800 <puts@plt>
void* io_thread(void *arg) {
    cd3c:	48 8b 5c 24 58       	mov    0x58(%rsp),%rbx
    cd41:	48 39 9c 24 98 00 00 00 	cmp    %rbx,0x98(%rsp)
    cd49:	0f 85 53 07 00 00    	jne    d4a2 <io_thread+0x1742>
    cd4f:	48 8d bd 34 80 ff 7f 	lea    0x7fff8034(%rbp),%rdi
    cd56:	66 0f ef c0          	pxor   %xmm0,%xmm0
    cd5a:	48 8d 85 2c 80 ff 7f 	lea    0x7fff802c(%rbp),%rax
    cd61:	c7 85 10 80 ff 7f 00 00 00 00 	movl   $0x0,0x7fff8010(%rbp)
    cd6b:	48 83 e7 f8          	and    $0xfffffffffffffff8,%rdi
    cd6f:	0f 11 85 00 80 ff 7f 	movups %xmm0,0x7fff8000(%rbp)
    cd76:	48 c7 85 2c 80 ff 7f 00 00 00 00 	movq   $0x0,0x7fff802c(%rbp)
    cd81:	48 29 f8             	sub    %rdi,%rax
    cd84:	8d 88 9c 00 00 00    	lea    0x9c(%rax),%ecx
    cd8a:	48 c7 85 c0 80 ff 7f 00 00 00 00 	movq   $0x0,0x7fff80c0(%rbp)
    cd95:	89 c8                	mov    %ecx,%eax
    cd97:	c1 e8 03             	shr    $0x3,%eax
    cd9a:	89 c1                	mov    %eax,%ecx
    cd9c:	31 c0                	xor    %eax,%eax
    cd9e:	f3 48 ab             	rep stos %rax,%es:(%rdi)
}
    cda1:	48 8b 84 24 08 07 00 00 	mov    0x708(%rsp),%rax
    cda9:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    cdb2:	0f 85 10 07 00 00    	jne    d4c8 <io_thread+0x1768>
    cdb8:	48 81 c4 18 07 00 00 	add    $0x718,%rsp
    cdbf:	31 c0                	xor    %eax,%eax
    cdc1:	5b                   	pop    %rbx
    cdc2:	5d                   	pop    %rbp
    cdc3:	41 5c                	pop    %r12
    cdc5:	41 5d                	pop    %r13
    cdc7:	41 5e                	pop    %r14
    cdc9:	41 5f                	pop    %r15
    cdcb:	c3                   	ret
    cdcc:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    cdd0:	48 c1 ea 03          	shr    $0x3,%rdx
    cdd4:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    cddb:	48 89 fa             	mov    %rdi,%rdx
    cdde:	83 e2 07             	and    $0x7,%edx
    cde1:	83 c2 03             	add    $0x3,%edx
    cde4:	40 38 f2             	cmp    %sil,%dl
    cde7:	7c 09                	jl     cdf2 <io_thread+0x1092>
    cde9:	40 84 f6             	test   %sil,%sil
    cdec:	0f 85 41 07 00 00    	jne    d533 <io_thread+0x17d3>
    cdf2:	8b 17                	mov    (%rdi),%edx
    cdf4:	e9 bc f4 ff ff       	jmp    c2b5 <io_thread+0x555>
    cdf9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
	*cqe_ptr = cqe;
    ce00:	4c 8d bb e0 f9 ff ff 	lea    -0x620(%rbx),%r15
    ce07:	4c 89 f8             	mov    %r15,%rax
    ce0a:	48 c1 e8 03          	shr    $0x3,%rax
    ce0e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ce15:	0f 85 ef 04 00 00    	jne    d30a <io_thread+0x15aa>
    ce1b:	48 89 bb e0 f9 ff ff 	mov    %rdi,-0x620(%rbx)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    ce22:	48 85 ff             	test   %rdi,%rdi
    ce25:	0f 84 bd f9 ff ff    	je     c7e8 <io_thread+0xa88>
      if (cqe->user_data == 1) {
    ce2b:	48 89 f8             	mov    %rdi,%rax
    ce2e:	48 c1 e8 03          	shr    $0x3,%rax
    ce32:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ce39:	0f 85 8e 05 00 00    	jne    d3cd <io_thread+0x166d>
    ce3f:	48 83 3f 01          	cmpq   $0x1,(%rdi)
    ce43:	0f 84 e7 03 00 00    	je     d230 <io_thread+0x14d0>
    ce49:	48 8d 3d 50 4e 00 00 	lea    0x4e50(%rip),%rdi        # 11ca0 <_IO_stdin_used+0xca0>
    ce50:	e8 ab 79 ff ff       	call   4800 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    ce55:	4c 89 f8             	mov    %r15,%rax
    ce58:	48 c1 e8 03          	shr    $0x3,%rax
    ce5c:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ce63:	0f 85 69 05 00 00    	jne    d3d2 <io_thread+0x1672>
    ce69:	48 8b bb e0 f9 ff ff 	mov    -0x620(%rbx),%rdi
    ce70:	48 89 f8             	mov    %rdi,%rax
    ce73:	48 c1 e8 03          	shr    $0x3,%rax
    ce77:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ce7e:	0f 85 56 05 00 00    	jne    d3da <io_thread+0x167a>
    ce84:	4c 8b 37             	mov    (%rdi),%r14
      if (ret < 0)
    ce87:	e9 f3 f9 ff ff       	jmp    c87f <io_thread+0xb1f>
    ce8c:	0f 1f 40 00          	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    ce90:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    ce95:	48 c1 e8 03          	shr    $0x3,%rax
    ce99:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    cea0:	0f 85 39 05 00 00    	jne    d3df <io_thread+0x167f>
    cea6:	48 8b bb a8 fa ff ff 	mov    -0x558(%rbx),%rdi
    cead:	48 89 f8             	mov    %rdi,%rax
    ceb0:	48 c1 e8 03          	shr    $0x3,%rax
    ceb4:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    cebb:	48 89 f8             	mov    %rdi,%rax
    cebe:	83 e0 07             	and    $0x7,%eax
    cec1:	83 c0 03             	add    $0x3,%eax
    cec4:	38 d0                	cmp    %dl,%al
    cec6:	7c 08                	jl     ced0 <io_thread+0x1170>
    cec8:	84 d2                	test   %dl,%dl
    ceca:	0f 85 19 05 00 00    	jne    d3e9 <io_thread+0x1689>
    ced0:	8b 07                	mov    (%rdi),%eax
    ced2:	83 c0 01             	add    $0x1,%eax
    ced5:	89 07                	mov    %eax,(%rdi)
}
    ced7:	e9 98 fa ff ff       	jmp    c974 <io_thread+0xc14>
    cedc:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    cee0:	48 c1 ea 03          	shr    $0x3,%rdx
    cee4:	0f b6 b2 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%esi
    ceeb:	48 89 fa             	mov    %rdi,%rdx
    ceee:	83 e2 07             	and    $0x7,%edx
    cef1:	83 c2 03             	add    $0x3,%edx
    cef4:	40 38 f2             	cmp    %sil,%dl
    cef7:	7c 09                	jl     cf02 <io_thread+0x11a2>
    cef9:	40 84 f6             	test   %sil,%sil
    cefc:	0f 85 93 03 00 00    	jne    d295 <io_thread+0x1535>
    cf02:	8b 17                	mov    (%rdi),%edx
    cf04:	e9 10 fb ff ff       	jmp    ca19 <io_thread+0xcb9>
    cf09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
              for (int i = 0; i < req->iovec_count; i++) {
    cf10:	49 8d 7e 04          	lea    0x4(%r14),%rdi
    cf14:	48 89 f8             	mov    %rdi,%rax
    cf17:	48 c1 e8 03          	shr    $0x3,%rax
    cf1b:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    cf22:	48 89 f8             	mov    %rdi,%rax
    cf25:	83 e0 07             	and    $0x7,%eax
    cf28:	83 c0 03             	add    $0x3,%eax
    cf2b:	38 d0                	cmp    %dl,%al
    cf2d:	7c 08                	jl     cf37 <io_thread+0x11d7>
    cf2f:	84 d2                	test   %dl,%dl
    cf31:	0f 85 89 04 00 00    	jne    d3c0 <io_thread+0x1660>
    cf37:	49 89 fc             	mov    %rdi,%r12
    cf3a:	45 8b 46 04          	mov    0x4(%r14),%r8d
    cf3e:	48 89 f8             	mov    %rdi,%rax
    cf41:	49 8d 6e 10          	lea    0x10(%r14),%rbp
    cf45:	41 83 e4 07          	and    $0x7,%r12d
    cf49:	45 31 ed             	xor    %r13d,%r13d
    cf4c:	48 c1 e8 03          	shr    $0x3,%rax
    cf50:	41 83 c4 03          	add    $0x3,%r12d
    cf54:	45 85 c0             	test   %r8d,%r8d
    cf57:	7e 5d                	jle    cfb6 <io_thread+0x1256>
    cf59:	48 89 bc 24 a0 00 00 00 	mov    %rdi,0xa0(%rsp)
    cf61:	48 89 9c 24 88 00 00 00 	mov    %rbx,0x88(%rsp)
    cf69:	48 89 eb             	mov    %rbp,%rbx
    cf6c:	48 89 c5             	mov    %rax,%rbp
    cf6f:	90                   	nop
                  free(req->iov[i].iov_base);
    cf70:	48 89 d9             	mov    %rbx,%rcx
    cf73:	48 c1 e9 03          	shr    $0x3,%rcx
    cf77:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    cf7e:	0f 85 16 03 00 00    	jne    d29a <io_thread+0x153a>
    cf84:	48 8b 3b             	mov    (%rbx),%rdi
              for (int i = 0; i < req->iovec_count; i++) {
    cf87:	41 83 c5 01          	add    $0x1,%r13d
                  free(req->iov[i].iov_base);
    cf8b:	e8 10 78 ff ff       	call   47a0 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    cf90:	0f b6 8d 00 80 ff 7f 	movzbl 0x7fff8000(%rbp),%ecx
    cf97:	41 38 cc             	cmp    %cl,%r12b
    cf9a:	7c 08                	jl     cfa4 <io_thread+0x1244>
    cf9c:	84 c9                	test   %cl,%cl
    cf9e:	0f 85 fe 02 00 00    	jne    d2a2 <io_thread+0x1542>
    cfa4:	48 83 c3 10          	add    $0x10,%rbx
    cfa8:	45 39 6e 04          	cmp    %r13d,0x4(%r14)
    cfac:	7f c2                	jg     cf70 <io_thread+0x1210>
    cfae:	48 8b 9c 24 88 00 00 00 	mov    0x88(%rsp),%rbx
              close(req->client_socket);
    cfb6:	49 8d 7e 08          	lea    0x8(%r14),%rdi
    cfba:	48 89 f8             	mov    %rdi,%rax
    cfbd:	48 c1 e8 03          	shr    $0x3,%rax
    cfc1:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    cfc8:	84 c0                	test   %al,%al
    cfca:	74 08                	je     cfd4 <io_thread+0x1274>
    cfcc:	3c 03                	cmp    $0x3,%al
    cfce:	0f 8e 5f 04 00 00    	jle    d433 <io_thread+0x16d3>
    cfd4:	41 8b 7e 08          	mov    0x8(%r14),%edi
    cfd8:	e8 b3 74 ff ff       	call   4490 <close@plt>
              free(req);
    cfdd:	4c 89 f7             	mov    %r14,%rdi
    cfe0:	e8 bb 77 ff ff       	call   47a0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    cfe5:	4c 89 f8             	mov    %r15,%rax
    cfe8:	48 c1 e8 03          	shr    $0x3,%rax
    cfec:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    cff3:	0f 84 6b f9 ff ff    	je     c964 <io_thread+0xc04>
    cff9:	4c 89 ff             	mov    %r15,%rdi
    cffc:	e8 df 74 ff ff       	call   44e0 <__asan_report_load8@plt>
    d001:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
              if (!cqe->res) {
    d008:	85 c0                	test   %eax,%eax
    d00a:	75 54                	jne    d060 <io_thread+0x1300>
                  fprintf(stderr, "Empty request!\n");
    d00c:	48 8d 3d 0d 9b 00 00 	lea    0x9b0d(%rip),%rdi        # 16b20 <stderr@GLIBC_2.2.5>
    d013:	48 89 f8             	mov    %rdi,%rax
    d016:	48 c1 e8 03          	shr    $0x3,%rax
    d01a:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d021:	0f 85 49 06 00 00    	jne    d670 <io_thread+0x1910>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    d027:	48 8b 0d f2 9a 00 00 	mov    0x9af2(%rip),%rcx        # 16b20 <stderr@GLIBC_2.2.5>
    d02e:	ba 0f 00 00 00       	mov    $0xf,%edx
    d033:	be 01 00 00 00       	mov    $0x1,%esi
    d038:	48 8d 3d 41 4d 00 00 	lea    0x4d41(%rip),%rdi        # 11d80 <_IO_stdin_used+0xd80>
    d03f:	e8 5c 74 ff ff       	call   44a0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    d044:	4c 89 f8             	mov    %r15,%rax
    d047:	48 c1 e8 03          	shr    $0x3,%rax
    d04b:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d052:	0f 84 0c f9 ff ff    	je     c964 <io_thread+0xc04>
    d058:	4c 89 ff             	mov    %r15,%rdi
    d05b:	e8 80 74 ff ff       	call   44e0 <__asan_report_load8@plt>
    char http_request[1024];
    d060:	4c 8d ab 60 fb ff ff 	lea    -0x4a0(%rbx),%r13
    d067:	be 00 04 00 00       	mov    $0x400,%esi
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
    d06c:	4d 8d 66 10          	lea    0x10(%r14),%r12
    char http_request[1024];
    d070:	4c 89 ef             	mov    %r13,%rdi
    d073:	e8 f8 74 ff ff       	call   4570 <__asan_unpoison_stack_memory@plt>
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
    d078:	4c 89 e0             	mov    %r12,%rax
    d07b:	48 c1 e8 03          	shr    $0x3,%rax
    d07f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d086:	0f 85 6d 05 00 00    	jne    d5f9 <io_thread+0x1899>
    for (int i = 0; i < dest_sz; i++) {
    d08c:	49 8b 46 10          	mov    0x10(%r14),%rax
    d090:	4c 89 ef             	mov    %r13,%rdi
    d093:	4c 8d 83 60 ff ff ff 	lea    -0xa0(%rbx),%r8
    d09a:	eb 14                	jmp    d0b0 <io_thread+0x1350>
    d09c:	0f 1f 40 00          	nopl   0x0(%rax)
    d0a0:	48 83 c7 01          	add    $0x1,%rdi
    d0a4:	48 89 f0             	mov    %rsi,%rax
    d0a7:	49 39 f8             	cmp    %rdi,%r8
    d0aa:	0f 84 00 01 00 00    	je     d1b0 <io_thread+0x1450>
        dest[i] = src[i];
    d0b0:	48 89 c2             	mov    %rax,%rdx
    d0b3:	48 89 c1             	mov    %rax,%rcx
    d0b6:	48 c1 ea 03          	shr    $0x3,%rdx
    d0ba:	83 e1 07             	and    $0x7,%ecx
    d0bd:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    d0c4:	38 ca                	cmp    %cl,%dl
    d0c6:	7f 08                	jg     d0d0 <io_thread+0x1370>
    d0c8:	84 d2                	test   %dl,%dl
    d0ca:	0f 85 df 01 00 00    	jne    d2af <io_thread+0x154f>
    d0d0:	48 89 f9             	mov    %rdi,%rcx
    d0d3:	48 89 fe             	mov    %rdi,%rsi
    d0d6:	0f b6 10             	movzbl (%rax),%edx
    d0d9:	48 c1 e9 03          	shr    $0x3,%rcx
    d0dd:	83 e6 07             	and    $0x7,%esi
    d0e0:	0f b6 89 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%ecx
    d0e7:	40 38 f1             	cmp    %sil,%cl
    d0ea:	7f 08                	jg     d0f4 <io_thread+0x1394>
    d0ec:	84 c9                	test   %cl,%cl
    d0ee:	0f 85 c3 01 00 00    	jne    d2b7 <io_thread+0x1557>
    d0f4:	88 17                	mov    %dl,(%rdi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    d0f6:	48 8d 70 01          	lea    0x1(%rax),%rsi
    d0fa:	80 fa 0d             	cmp    $0xd,%dl
    d0fd:	75 a1                	jne    d0a0 <io_thread+0x1340>
    d0ff:	48 89 f2             	mov    %rsi,%rdx
    d102:	48 89 f1             	mov    %rsi,%rcx
    d105:	48 c1 ea 03          	shr    $0x3,%rdx
    d109:	83 e1 07             	and    $0x7,%ecx
    d10c:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    d113:	38 ca                	cmp    %cl,%dl
    d115:	7f 08                	jg     d11f <io_thread+0x13bf>
    d117:	84 d2                	test   %dl,%dl
    d119:	0f 85 99 02 00 00    	jne    d3b8 <io_thread+0x1658>
    d11f:	80 78 01 0a          	cmpb   $0xa,0x1(%rax)
    d123:	0f 85 77 ff ff ff    	jne    d0a0 <io_thread+0x1340>
            dest[i] = '\0';
    d129:	c6 07 00             	movb   $0x0,(%rdi)
    handle_http_method(http_request, req->client_socket, ring);
    d12c:	49 8d 7e 08          	lea    0x8(%r14),%rdi
    d130:	48 89 f8             	mov    %rdi,%rax
    d133:	48 c1 e8 03          	shr    $0x3,%rax
    d137:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    d13e:	84 c0                	test   %al,%al
    d140:	74 08                	je     d14a <io_thread+0x13ea>
    d142:	3c 03                	cmp    $0x3,%al
    d144:	0f 8e a0 03 00 00    	jle    d4ea <io_thread+0x178a>
    d14a:	41 8b 76 08          	mov    0x8(%r14),%esi
    d14e:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    d153:	4c 89 ef             	mov    %r13,%rdi
    d156:	e8 35 e2 ff ff       	call   b390 <handle_http_method>
    return 0;
    d15b:	be 00 04 00 00       	mov    $0x400,%esi
    d160:	4c 89 ef             	mov    %r13,%rdi
    d163:	e8 e8 72 ff ff       	call   4450 <__asan_poison_stack_memory@plt>
              free(req->iov[0].iov_base);
    d168:	4c 89 e0             	mov    %r12,%rax
    d16b:	48 c1 e8 03          	shr    $0x3,%rax
    d16f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d176:	0f 85 66 03 00 00    	jne    d4e2 <io_thread+0x1782>
    d17c:	49 8b 7e 10          	mov    0x10(%r14),%rdi
    d180:	e8 1b 76 ff ff       	call   47a0 <free@plt>
              free(req);
    d185:	4c 89 f7             	mov    %r14,%rdi
    d188:	e8 13 76 ff ff       	call   47a0 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    d18d:	4c 89 f8             	mov    %r15,%rax
    d190:	48 c1 e8 03          	shr    $0x3,%rax
    d194:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d19b:	0f 84 c3 f7 ff ff    	je     c964 <io_thread+0xc04>
    d1a1:	4c 89 ff             	mov    %r15,%rdi
    d1a4:	e8 37 73 ff ff       	call   44e0 <__asan_report_load8@plt>
    d1a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        fprintf(stderr, "Malformed request\n");
    d1b0:	48 8d 3d 69 99 00 00 	lea    0x9969(%rip),%rdi        # 16b20 <stderr@GLIBC_2.2.5>
    d1b7:	48 89 f8             	mov    %rdi,%rax
    d1ba:	48 c1 e8 03          	shr    $0x3,%rax
    d1be:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d1c5:	0f 85 12 03 00 00    	jne    d4dd <io_thread+0x177d>
    d1cb:	48 8b 0d 4e 99 00 00 	mov    0x994e(%rip),%rcx        # 16b20 <stderr@GLIBC_2.2.5>
    d1d2:	ba 12 00 00 00       	mov    $0x12,%edx
    d1d7:	be 01 00 00 00       	mov    $0x1,%esi
    d1dc:	48 8d 3d bd 48 00 00 	lea    0x48bd(%rip),%rdi        # 11aa0 <_IO_stdin_used+0xaa0>
    d1e3:	e8 b8 72 ff ff       	call   44a0 <fwrite@plt>
        exit(1);
    d1e8:	e8 23 74 ff ff       	call   4610 <__asan_handle_no_return@plt>
    d1ed:	bf 01 00 00 00       	mov    $0x1,%edi
    d1f2:	e8 19 73 ff ff       	call   4510 <exit@plt>
    d1f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    d200:	4c 8d bb e0 f9 ff ff 	lea    -0x620(%rbx),%r15
    d207:	4c 89 f8             	mov    %r15,%rax
    d20a:	48 c1 e8 03          	shr    $0x3,%rax
    d20e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d215:	0f 85 75 02 00 00    	jne    d490 <io_thread+0x1730>
    d21b:	48 89 bb e0 f9 ff ff 	mov    %rdi,-0x620(%rbx)
	return err;
    d222:	e9 04 fc ff ff       	jmp    ce2b <io_thread+0x10cb>
    d227:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    d230:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    d235:	48 8b ac 24 a8 00 00 00 	mov    0xa8(%rsp),%rbp
    d23d:	48 c1 e8 03          	shr    $0x3,%rax
    d241:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d248:	0f 85 b3 03 00 00    	jne    d601 <io_thread+0x18a1>
    d24e:	48 8b bb a8 fa ff ff 	mov    -0x558(%rbx),%rdi
    d255:	48 89 f8             	mov    %rdi,%rax
    d258:	48 c1 e8 03          	shr    $0x3,%rax
    d25c:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    d263:	48 89 f8             	mov    %rdi,%rax
    d266:	83 e0 07             	and    $0x7,%eax
    d269:	83 c0 03             	add    $0x3,%eax
    d26c:	38 d0                	cmp    %dl,%al
    d26e:	7c 08                	jl     d278 <io_thread+0x1518>
    d270:	84 d2                	test   %dl,%dl
    d272:	0f 85 20 02 00 00    	jne    d498 <io_thread+0x1738>
    d278:	8b 07                	mov    (%rdi),%eax
    d27a:	83 c0 01             	add    $0x1,%eax
    d27d:	89 07                	mov    %eax,(%rdi)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    d27f:	48 8d 3d da 49 00 00 	lea    0x49da(%rip),%rdi        # 11c60 <_IO_stdin_used+0xc60>
    d286:	e8 75 75 ff ff       	call   4800 <puts@plt>
    d28b:	e9 a0 fa ff ff       	jmp    cd30 <io_thread+0xfd0>
		head = IO_URING_READ_ONCE(*sq->khead);
    d290:	e8 bb 72 ff ff       	call   4550 <__asan_report_load4@plt>
		head = io_uring_smp_load_acquire(sq->khead);
    d295:	e8 b6 72 ff ff       	call   4550 <__asan_report_load4@plt>
                  free(req->iov[i].iov_base);
    d29a:	48 89 df             	mov    %rbx,%rdi
    d29d:	e8 3e 72 ff ff       	call   44e0 <__asan_report_load8@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    d2a2:	48 8b bc 24 a0 00 00 00 	mov    0xa0(%rsp),%rdi
    d2aa:	e8 a1 72 ff ff       	call   4550 <__asan_report_load4@plt>
        dest[i] = src[i];
    d2af:	48 89 c7             	mov    %rax,%rdi
    d2b2:	e8 d9 74 ff ff       	call   4790 <__asan_report_load1@plt>
    d2b7:	e8 14 75 ff ff       	call   47d0 <__asan_report_store1@plt>
				cqe->user_data == LIBURING_UDATA_TIMEOUT) {
    d2bc:	e8 1f 72 ff ff       	call   44e0 <__asan_report_load8@plt>
			if (cqe->res < 0)
    d2c1:	4c 89 c7             	mov    %r8,%rdi
    d2c4:	e8 87 72 ff ff       	call   4550 <__asan_report_load4@plt>
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    d2c9:	4c 89 f7             	mov    %r14,%rdi
    d2cc:	e8 0f 72 ff ff       	call   44e0 <__asan_report_load8@plt>
    d2d1:	e8 7a 72 ff ff       	call   4550 <__asan_report_load4@plt>
		unsigned head = *ring->cq.khead;
    d2d6:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
    d2db:	e8 00 72 ff ff       	call   44e0 <__asan_report_load8@plt>
    d2e0:	48 89 d7             	mov    %rdx,%rdi
    d2e3:	e8 68 72 ff ff       	call   4550 <__asan_report_load4@plt>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    d2e8:	4c 89 ef             	mov    %r13,%rdi
    d2eb:	e8 f0 71 ff ff       	call   44e0 <__asan_report_load8@plt>
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    d2f0:	48 89 f7             	mov    %rsi,%rdi
    d2f3:	e8 58 72 ff ff       	call   4550 <__asan_report_load4@plt>
	if (next - head <= sq->ring_entries) {
    d2f8:	4c 89 df             	mov    %r11,%rdi
    d2fb:	e8 50 72 ff ff       	call   4550 <__asan_report_load4@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    d300:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    d305:	e8 46 72 ff ff       	call   4550 <__asan_report_load4@plt>
	*cqe_ptr = cqe;
    d30a:	4c 89 ff             	mov    %r15,%rdi
    d30d:	e8 be 73 ff ff       	call   46d0 <__asan_report_store8@plt>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    d312:	4c 89 f7             	mov    %r14,%rdi
    d315:	e8 36 72 ff ff       	call   4550 <__asan_report_load4@plt>
    d31a:	f7 d8                	neg    %eax
    d31c:	89 c7                	mov    %eax,%edi
    d31e:	e8 bd 74 ff ff       	call   47e0 <strerror@plt>
    d323:	48 8d 3d f6 97 00 00 	lea    0x97f6(%rip),%rdi        # 16b20 <stderr@GLIBC_2.2.5>
    d32a:	48 89 c1             	mov    %rax,%rcx
    d32d:	48 89 f8             	mov    %rdi,%rax
    d330:	48 c1 e8 03          	shr    $0x3,%rax
    d334:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d33b:	0f 85 5c 01 00 00    	jne    d49d <io_thread+0x173d>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    d341:	48 8b 3d d8 97 00 00 	mov    0x97d8(%rip),%rdi        # 16b20 <stderr@GLIBC_2.2.5>
    d348:	45 89 e0             	mov    %r12d,%r8d
    d34b:	be 01 00 00 00       	mov    $0x1,%esi
    d350:	31 c0                	xor    %eax,%eax
    d352:	48 8d 15 c7 49 00 00 	lea    0x49c7(%rip),%rdx        # 11d20 <_IO_stdin_used+0xd20>
    d359:	e8 f2 73 ff ff       	call   4750 <__fprintf_chk@plt>
          exit(1);
    d35e:	e8 ad 72 ff ff       	call   4610 <__asan_handle_no_return@plt>
    d363:	bf 01 00 00 00       	mov    $0x1,%edi
    d368:	e8 a3 71 ff ff       	call   4510 <exit@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    d36d:	48 89 f7             	mov    %rsi,%rdi
    d370:	e8 db 71 ff ff       	call   4550 <__asan_report_load4@plt>
	if (ring->flags & IORING_SETUP_SQE128)
    d375:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    d37a:	e8 d1 71 ff ff       	call   4550 <__asan_report_load4@plt>
		head = IO_URING_READ_ONCE(*sq->khead);
    d37f:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    d384:	e8 57 71 ff ff       	call   44e0 <__asan_report_load8@plt>
	unsigned mask = ring->cq.ring_mask;
    d389:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    d38e:	e8 bd 71 ff ff       	call   4550 <__asan_report_load4@plt>
      if (cqe->res < 0) {
    d393:	48 89 d7             	mov    %rdx,%rdi
    d396:	e8 b5 71 ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->user_data = (unsigned long) data;
    d39b:	48 89 c7             	mov    %rax,%rdi
    d39e:	e8 2d 73 ff ff       	call   46d0 <__asan_report_store8@plt>
  while (data->running == 1) {
    d3a3:	48 89 f7             	mov    %rsi,%rdi
    d3a6:	e8 a5 71 ff ff       	call   4550 <__asan_report_load4@plt>
              add_read_request(cqe->res, &ring);
    d3ab:	4c 89 ff             	mov    %r15,%rdi
    d3ae:	e8 2d 71 ff ff       	call   44e0 <__asan_report_load8@plt>
    d3b3:	e8 98 71 ff ff       	call   4550 <__asan_report_load4@plt>
        if (src[i] == '\r' && src[i+1] == '\n') {
    d3b8:	48 89 f7             	mov    %rsi,%rdi
    d3bb:	e8 d0 73 ff ff       	call   4790 <__asan_report_load1@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    d3c0:	e8 8b 71 ff ff       	call   4550 <__asan_report_load4@plt>
      io_uring_cqe_seen(&ring, cqe);
    d3c5:	4c 89 ff             	mov    %r15,%rdi
    d3c8:	e8 13 71 ff ff       	call   44e0 <__asan_report_load8@plt>
      if (cqe->user_data == 1) {
    d3cd:	e8 0e 71 ff ff       	call   44e0 <__asan_report_load8@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    d3d2:	4c 89 ff             	mov    %r15,%rdi
    d3d5:	e8 06 71 ff ff       	call   44e0 <__asan_report_load8@plt>
    d3da:	e8 01 71 ff ff       	call   44e0 <__asan_report_load8@plt>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    d3df:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
    d3e4:	e8 f7 70 ff ff       	call   44e0 <__asan_report_load8@plt>
    d3e9:	e8 62 71 ff ff       	call   4550 <__asan_report_load4@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    d3ee:	48 8b 7c 24 78       	mov    0x78(%rsp),%rdi
    d3f3:	e8 58 71 ff ff       	call   4550 <__asan_report_load4@plt>
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    d3f8:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    d3fd:	e8 4e 71 ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->opcode = (__u8) op;
    d402:	e8 c9 73 ff ff       	call   47d0 <__asan_report_store1@plt>
	sqe->flags = 0;
    d407:	48 89 c7             	mov    %rax,%rdi
    d40a:	e8 c1 73 ff ff       	call   47d0 <__asan_report_store1@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    d40f:	48 8b 7c 24 70       	mov    0x70(%rsp),%rdi
    d414:	e8 c7 70 ff ff       	call   44e0 <__asan_report_load8@plt>
      if (cqe->user_data == 1) {
    d419:	4c 89 ff             	mov    %r15,%rdi
    d41c:	e8 bf 70 ff ff       	call   44e0 <__asan_report_load8@plt>
    d421:	e8 ba 70 ff ff       	call   44e0 <__asan_report_load8@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    d426:	4c 89 ff             	mov    %r15,%rdi
    d429:	e8 b2 70 ff ff       	call   44e0 <__asan_report_load8@plt>
    d42e:	e8 ad 70 ff ff       	call   44e0 <__asan_report_load8@plt>
              close(req->client_socket);
    d433:	e8 18 71 ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->ioprio = 0;
    d438:	48 89 d7             	mov    %rdx,%rdi
    d43b:	e8 c0 70 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->fd = fd;
    d440:	48 89 d7             	mov    %rdx,%rdi
    d443:	e8 78 72 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->off = offset;
    d448:	48 89 c7             	mov    %rax,%rdi
    d44b:	e8 80 72 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->addr = (unsigned long) addr;
    d450:	48 89 c7             	mov    %rax,%rdi
    d453:	e8 78 72 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->len = len;
    d458:	48 89 d7             	mov    %rdx,%rdi
    d45b:	e8 60 72 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->rw_flags = 0;
    d460:	48 89 d7             	mov    %rdx,%rdi
    d463:	e8 58 72 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->buf_index = 0;
    d468:	48 89 d7             	mov    %rdx,%rdi
    d46b:	e8 90 70 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->personality = 0;
    d470:	48 89 d7             	mov    %rdx,%rdi
    d473:	e8 88 70 ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->file_index = 0;
    d478:	48 89 d7             	mov    %rdx,%rdi
    d47b:	e8 40 72 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->addr3 = 0;
    d480:	48 89 c7             	mov    %rax,%rdi
    d483:	e8 48 72 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->__pad2[0] = 0;
    d488:	48 89 c7             	mov    %rax,%rdi
    d48b:	e8 40 72 ff ff       	call   46d0 <__asan_report_store8@plt>
	*cqe_ptr = cqe;
    d490:	4c 89 ff             	mov    %r15,%rdi
    d493:	e8 38 72 ff ff       	call   46d0 <__asan_report_store8@plt>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    d498:	e8 b3 70 ff ff       	call   4550 <__asan_report_load4@plt>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    d49d:	e8 3e 70 ff ff       	call   44e0 <__asan_report_load8@plt>
void* io_thread(void *arg) {
    d4a2:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    d4a7:	be 40 06 00 00       	mov    $0x640,%esi
    d4ac:	48 c7 00 0e 36 e0 45 	movq   $0x45e0360e,(%rax)
    d4b3:	48 8b 94 24 98 00 00 00 	mov    0x98(%rsp),%rdx
    d4bb:	48 89 c7             	mov    %rax,%rdi
    d4be:	e8 bd 71 ff ff       	call   4680 <__asan_stack_free_5@plt>
    d4c3:	e9 d9 f8 ff ff       	jmp    cda1 <io_thread+0x1041>
}
    d4c8:	e8 e3 71 ff ff       	call   46b0 <__stack_chk_fail@plt>
	sqe->__pad2[0] = 0;
    d4cd:	48 89 c7             	mov    %rax,%rdi
    d4d0:	e8 fb 71 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->user_data = (unsigned long) data;
    d4d5:	48 89 c7             	mov    %rax,%rdi
    d4d8:	e8 f3 71 ff ff       	call   46d0 <__asan_report_store8@plt>
        fprintf(stderr, "Malformed request\n");
    d4dd:	e8 fe 6f ff ff       	call   44e0 <__asan_report_load8@plt>
              free(req->iov[0].iov_base);
    d4e2:	4c 89 e7             	mov    %r12,%rdi
    d4e5:	e8 f6 6f ff ff       	call   44e0 <__asan_report_load8@plt>
    handle_http_method(http_request, req->client_socket, ring);
    d4ea:	e8 61 70 ff ff       	call   4550 <__asan_report_load4@plt>
  io_uring_register_eventfd(data->ring, 0);
    d4ef:	4c 89 e7             	mov    %r12,%rdi
    d4f2:	e8 e9 6f ff ff       	call   44e0 <__asan_report_load8@plt>
  struct io_uring ring = *data->ring;
    d4f7:	be d8 00 00 00       	mov    $0xd8,%esi
    d4fc:	e8 5f 70 ff ff       	call   4560 <__asan_report_load_n@plt>
    d501:	be d8 00 00 00       	mov    $0xd8,%esi
    d506:	48 89 cf             	mov    %rcx,%rdi
    d509:	e8 72 70 ff ff       	call   4580 <__asan_report_store_n@plt>
    d50e:	4c 89 e7             	mov    %r12,%rdi
    d511:	e8 ca 6f ff ff       	call   44e0 <__asan_report_load8@plt>
void* io_thread(void *arg) {
    d516:	bf 40 06 00 00       	mov    $0x640,%edi
    d51b:	e8 50 72 ff ff       	call   4770 <__asan_stack_malloc_5@plt>
    d520:	48 85 c0             	test   %rax,%rax
    d523:	48 0f 44 44 24 58    	cmove  0x58(%rsp),%rax
    d529:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    d52e:	e9 6c e8 ff ff       	jmp    bd9f <io_thread+0x3f>
		head = io_uring_smp_load_acquire(sq->khead);
    d533:	e8 18 70 ff ff       	call   4550 <__asan_report_load4@plt>
		head = IO_URING_READ_ONCE(*sq->khead);
    d538:	e8 13 70 ff ff       	call   4550 <__asan_report_load4@plt>
	if (next - head <= sq->ring_entries) {
    d53d:	4c 89 d7             	mov    %r10,%rdi
    d540:	e8 0b 70 ff ff       	call   4550 <__asan_report_load4@plt>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    d545:	48 89 f7             	mov    %rsi,%rdi
    d548:	e8 93 6f ff ff       	call   44e0 <__asan_report_load8@plt>
    d54d:	48 8b 7c 24 78       	mov    0x78(%rsp),%rdi
    d552:	e8 f9 6f ff ff       	call   4550 <__asan_report_load4@plt>
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    d557:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    d55c:	e8 ef 6f ff ff       	call   4550 <__asan_report_load4@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    d561:	48 89 f7             	mov    %rsi,%rdi
    d564:	e8 e7 6f ff ff       	call   4550 <__asan_report_load4@plt>
  iov->iov_len = 10;
    d569:	e8 62 71 ff ff       	call   46d0 <__asan_report_store8@plt>
  iov->iov_base = zh_malloc(10);
    d56e:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    d573:	e8 58 71 ff ff       	call   46d0 <__asan_report_store8@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    d578:	48 8d 3d a1 95 00 00 	lea    0x95a1(%rip),%rdi        # 16b20 <stderr@GLIBC_2.2.5>
    d57f:	48 89 f8             	mov    %rdi,%rax
    d582:	48 c1 e8 03          	shr    $0x3,%rax
    d586:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d58d:	75 65                	jne    d5f4 <io_thread+0x1894>
    d58f:	48 8b 0d 8a 95 00 00 	mov    0x958a(%rip),%rcx        # 16b20 <stderr@GLIBC_2.2.5>
    d596:	ba 28 00 00 00       	mov    $0x28,%edx
    d59b:	be 01 00 00 00       	mov    $0x1,%esi
    d5a0:	48 8d 3d f9 3c 00 00 	lea    0x3cf9(%rip),%rdi        # 112a0 <_IO_stdin_used+0x2a0>
    d5a7:	e8 f4 6e ff ff       	call   44a0 <fwrite@plt>
        exit(1);
    d5ac:	e8 5f 70 ff ff       	call   4610 <__asan_handle_no_return@plt>
    d5b1:	bf 01 00 00 00       	mov    $0x1,%edi
    d5b6:	e8 55 6f ff ff       	call   4510 <exit@plt>
  socklen_t client_addr_len = sizeof(client_addr);
    d5bb:	48 8b bc 24 80 00 00 00 	mov    0x80(%rsp),%rdi
    d5c3:	e8 f8 70 ff ff       	call   46c0 <__asan_report_store4@plt>
  int enable = 1;
    d5c8:	e8 f3 70 ff ff       	call   46c0 <__asan_report_store4@plt>
		head = IO_URING_READ_ONCE(*sq->khead);
    d5cd:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    d5d2:	e8 09 6f ff ff       	call   44e0 <__asan_report_load8@plt>
	if (ring->flags & IORING_SETUP_SQE128)
    d5d7:	48 89 f7             	mov    %rsi,%rdi
    d5da:	e8 71 6f ff ff       	call   4550 <__asan_report_load4@plt>
	*cqe_ptr = cqe;
    d5df:	4c 89 ff             	mov    %r15,%rdi
    d5e2:	e8 e9 70 ff ff       	call   46d0 <__asan_report_store8@plt>
  srv_addr.sin_port = htons(port);
    d5e7:	e8 14 6f ff ff       	call   4500 <__asan_report_store2@plt>
  srv_addr.sin_family = AF_INET;
    d5ec:	4c 89 e7             	mov    %r12,%rdi
    d5ef:	e8 0c 6f ff ff       	call   4500 <__asan_report_store2@plt>
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
    d5f4:	e8 e7 6e ff ff       	call   44e0 <__asan_report_load8@plt>
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
    d5f9:	4c 89 e7             	mov    %r12,%rdi
    d5fc:	e8 df 6e ff ff       	call   44e0 <__asan_report_load8@plt>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    d601:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
    d606:	e8 d5 6e ff ff       	call   44e0 <__asan_report_load8@plt>
  while (data->running == 1) {
    d60b:	48 89 f7             	mov    %rsi,%rdi
    d60e:	e8 3d 6f ff ff       	call   4550 <__asan_report_load4@plt>
	sqe->opcode = (__u8) op;
    d613:	e8 b8 71 ff ff       	call   47d0 <__asan_report_store1@plt>
	sqe->flags = 0;
    d618:	48 89 c7             	mov    %rax,%rdi
    d61b:	e8 b0 71 ff ff       	call   47d0 <__asan_report_store1@plt>
	sqe->ioprio = 0;
    d620:	48 89 d7             	mov    %rdx,%rdi
    d623:	e8 d8 6e ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->fd = fd;
    d628:	48 89 d7             	mov    %rdx,%rdi
    d62b:	e8 90 70 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->off = offset;
    d630:	48 89 c7             	mov    %rax,%rdi
    d633:	e8 98 70 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->addr = (unsigned long) addr;
    d638:	48 89 c7             	mov    %rax,%rdi
    d63b:	e8 90 70 ff ff       	call   46d0 <__asan_report_store8@plt>
	sqe->len = len;
    d640:	48 89 d7             	mov    %rdx,%rdi
    d643:	e8 78 70 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->rw_flags = 0;
    d648:	48 89 d7             	mov    %rdx,%rdi
    d64b:	e8 70 70 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->buf_index = 0;
    d650:	48 89 d7             	mov    %rdx,%rdi
    d653:	e8 a8 6e ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->personality = 0;
    d658:	48 89 d7             	mov    %rdx,%rdi
    d65b:	e8 a0 6e ff ff       	call   4500 <__asan_report_store2@plt>
	sqe->file_index = 0;
    d660:	48 89 d7             	mov    %rdx,%rdi
    d663:	e8 58 70 ff ff       	call   46c0 <__asan_report_store4@plt>
	sqe->addr3 = 0;
    d668:	48 89 c7             	mov    %rax,%rdi
    d66b:	e8 60 70 ff ff       	call   46d0 <__asan_report_store8@plt>
                  fprintf(stderr, "Empty request!\n");
    d670:	e8 6b 6e ff ff       	call   44e0 <__asan_report_load8@plt>
    d675:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

000000000000d680 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    d680:	f3 0f 1e fa          	endbr64
    d684:	41 57                	push   %r15
    d686:	41 56                	push   %r14
    d688:	41 55                	push   %r13
    d68a:	41 54                	push   %r12
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    d68c:	4c 8d a7 28 01 00 00 	lea    0x128(%rdi),%r12
int barriered_work_ingest(struct BarrierTask *data) {
    d693:	55                   	push   %rbp
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    d694:	4c 89 e0             	mov    %r12,%rax
int barriered_work_ingest(struct BarrierTask *data) {
    d697:	53                   	push   %rbx
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    d698:	48 c1 e8 03          	shr    $0x3,%rax
int barriered_work_ingest(struct BarrierTask *data) {
    d69c:	48 83 ec 18          	sub    $0x18,%rsp
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    d6a0:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d6a7:	0f 85 c5 03 00 00    	jne    da72 <barriered_work_ingest+0x3f2>
    d6ad:	4c 8b 97 28 01 00 00 	mov    0x128(%rdi),%r10
    d6b4:	49 89 fe             	mov    %rdi,%r14
    d6b7:	49 8d ba bc 00 00 00 	lea    0xbc(%r10),%rdi
    d6be:	48 89 f8             	mov    %rdi,%rax
    d6c1:	48 c1 e8 03          	shr    $0x3,%rax
    d6c5:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    d6cc:	48 89 f8             	mov    %rdi,%rax
    d6cf:	83 e0 07             	and    $0x7,%eax
    d6d2:	83 c0 03             	add    $0x3,%eax
    d6d5:	38 d0                	cmp    %dl,%al
    d6d7:	7c 08                	jl     d6e1 <barriered_work_ingest+0x61>
    d6d9:	84 d2                	test   %dl,%dl
    d6db:	0f 85 87 03 00 00    	jne    da68 <barriered_work_ingest+0x3e8>
    d6e1:	41 8b 92 bc 00 00 00 	mov    0xbc(%r10),%edx
    d6e8:	85 d2                	test   %edx,%edx
    d6ea:	0f 8e 13 01 00 00    	jle    d803 <barriered_work_ingest+0x183>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    d6f0:	49 8d 7a 50          	lea    0x50(%r10),%rdi
    d6f4:	48 89 f8             	mov    %rdi,%rax
    d6f7:	48 c1 e8 03          	shr    $0x3,%rax
    d6fb:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d702:	0f 85 5b 03 00 00    	jne    da63 <barriered_work_ingest+0x3e3>
        data->ingest_count++;
    d708:	49 8d 86 68 01 00 00 	lea    0x168(%r14),%rax
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    d70f:	4d 8b 5a 50          	mov    0x50(%r10),%r11
    d713:	45 31 ed             	xor    %r13d,%r13d
        data->ingest_count++;
    d716:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    d71b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    d720:	4e 8d 3c ed 00 00 00 00 	lea    0x0(,%r13,8),%r15
    d728:	4b 8d 3c 3b          	lea    (%r11,%r15,1),%rdi
    d72c:	48 89 f8             	mov    %rdi,%rax
    d72f:	48 c1 e8 03          	shr    $0x3,%rax
    d733:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d73a:	0f 85 e4 02 00 00    	jne    da24 <barriered_work_ingest+0x3a4>
    d740:	48 8b 3f             	mov    (%rdi),%rdi
    d743:	48 89 f8             	mov    %rdi,%rax
    d746:	48 c1 e8 03          	shr    $0x3,%rax
    d74a:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    d751:	84 c0                	test   %al,%al
    d753:	74 08                	je     d75d <barriered_work_ingest+0xdd>
    d755:	3c 03                	cmp    $0x3,%al
    d757:	0f 8e c2 02 00 00    	jle    da1f <barriered_work_ingest+0x39f>
    d75d:	8b 37                	mov    (%rdi),%esi
    d75f:	31 db                	xor    %ebx,%ebx
    d761:	4c 8d 4f 08          	lea    0x8(%rdi),%r9
    d765:	85 f6                	test   %esi,%esi
    d767:	0f 8e 89 00 00 00    	jle    d7f6 <barriered_work_ingest+0x176>
    d76d:	0f 1f 00             	nopl   (%rax)
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    d770:	4c 89 c8             	mov    %r9,%rax
    d773:	48 c1 e8 03          	shr    $0x3,%rax
    d777:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d77e:	0f 85 7c 02 00 00    	jne    da00 <barriered_work_ingest+0x380>
    d784:	48 8b 47 08          	mov    0x8(%rdi),%rax
    d788:	48 89 dd             	mov    %rbx,%rbp
    d78b:	48 c1 e5 08          	shl    $0x8,%rbp
    d78f:	48 01 e8             	add    %rbp,%rax
    d792:	48 8d 88 80 00 00 00 	lea    0x80(%rax),%rcx
    d799:	48 89 ca             	mov    %rcx,%rdx
    d79c:	48 c1 ea 03          	shr    $0x3,%rdx
    d7a0:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    d7a7:	84 d2                	test   %dl,%dl
    d7a9:	74 09                	je     d7b4 <barriered_work_ingest+0x134>
    d7ab:	80 fa 03             	cmp    $0x3,%dl
    d7ae:	0f 8e 54 02 00 00    	jle    da08 <barriered_work_ingest+0x388>
    d7b4:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    d7bb:	74 5b                	je     d818 <barriered_work_ingest+0x198>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    d7bd:	48 83 c3 01          	add    $0x1,%rbx
    d7c1:	39 de                	cmp    %ebx,%esi
    d7c3:	7f ab                	jg     d770 <barriered_work_ingest+0xf0>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    d7c5:	49 8d ba bc 00 00 00 	lea    0xbc(%r10),%rdi
    d7cc:	48 89 f8             	mov    %rdi,%rax
    d7cf:	48 c1 e8 03          	shr    $0x3,%rax
    d7d3:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    d7da:	48 89 f8             	mov    %rdi,%rax
    d7dd:	83 e0 07             	and    $0x7,%eax
    d7e0:	83 c0 03             	add    $0x3,%eax
    d7e3:	38 d0                	cmp    %dl,%al
    d7e5:	7c 08                	jl     d7ef <barriered_work_ingest+0x16f>
    d7e7:	84 d2                	test   %dl,%dl
    d7e9:	0f 85 7e 02 00 00    	jne    da6d <barriered_work_ingest+0x3ed>
    d7ef:	41 8b 92 bc 00 00 00 	mov    0xbc(%r10),%edx
    d7f6:	49 83 c5 01          	add    $0x1,%r13
    d7fa:	44 39 ea             	cmp    %r13d,%edx
    d7fd:	0f 8f 1d ff ff ff    	jg     d720 <barriered_work_ingest+0xa0>
}
    d803:	48 83 c4 18          	add    $0x18,%rsp
    d807:	31 c0                	xor    %eax,%eax
    d809:	5b                   	pop    %rbx
    d80a:	5d                   	pop    %rbp
    d80b:	41 5c                	pop    %r12
    d80d:	41 5d                	pop    %r13
    d80f:	41 5e                	pop    %r14
    d811:	41 5f                	pop    %r15
    d813:	c3                   	ret
    d814:	0f 1f 40 00          	nopl   0x0(%rax)
        data->ingest_count++;
    d818:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    d81d:	48 c1 ea 03          	shr    $0x3,%rdx
    d821:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    d828:	0f 85 e7 01 00 00    	jne    da15 <barriered_work_ingest+0x395>
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    d82e:	48 8d b8 88 00 00 00 	lea    0x88(%rax),%rdi
        data->ingest_count++;
    d835:	49 83 86 68 01 00 00 01 	addq   $0x1,0x168(%r14)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    d83d:	48 89 fa             	mov    %rdi,%rdx
    d840:	48 c1 ea 03          	shr    $0x3,%rdx
    d844:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    d84b:	0f 85 bf 01 00 00    	jne    da10 <barriered_work_ingest+0x390>
    d851:	48 8d b8 94 00 00 00 	lea    0x94(%rax),%rdi
    d858:	48 8b b0 88 00 00 00 	mov    0x88(%rax),%rsi
    d85f:	48 89 fa             	mov    %rdi,%rdx
    d862:	48 c1 ea 03          	shr    $0x3,%rdx
    d866:	0f b6 8a 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%ecx
    d86d:	48 89 fa             	mov    %rdi,%rdx
    d870:	83 e2 07             	and    $0x7,%edx
    d873:	83 c2 03             	add    $0x3,%edx
    d876:	38 ca                	cmp    %cl,%dl
    d878:	7c 08                	jl     d882 <barriered_work_ingest+0x202>
    d87a:	84 c9                	test   %cl,%cl
    d87c:	0f 85 b9 01 00 00    	jne    da3b <barriered_work_ingest+0x3bb>
    d882:	48 63 80 94 00 00 00 	movslq 0x94(%rax),%rax
    d889:	bf 04 00 00 00       	mov    $0x4,%edi
    d88e:	48 c1 e0 05          	shl    $0x5,%rax
    d892:	48 8d 74 06 10       	lea    0x10(%rsi,%rax,1),%rsi
    d897:	e8 e4 6b ff ff       	call   4480 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    d89c:	4c 89 e0             	mov    %r12,%rax
    d89f:	48 c1 e8 03          	shr    $0x3,%rax
    d8a3:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d8aa:	0f 85 83 01 00 00    	jne    da33 <barriered_work_ingest+0x3b3>
    d8b0:	49 8b 86 28 01 00 00 	mov    0x128(%r14),%rax
    d8b7:	48 8d 78 50          	lea    0x50(%rax),%rdi
    d8bb:	48 89 fa             	mov    %rdi,%rdx
    d8be:	48 c1 ea 03          	shr    $0x3,%rdx
    d8c2:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    d8c9:	0f 85 5f 01 00 00    	jne    da2e <barriered_work_ingest+0x3ae>
    d8cf:	48 8b 78 50          	mov    0x50(%rax),%rdi
    d8d3:	4c 01 ff             	add    %r15,%rdi
    d8d6:	48 89 f8             	mov    %rdi,%rax
    d8d9:	48 c1 e8 03          	shr    $0x3,%rax
    d8dd:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d8e4:	0f 85 3f 01 00 00    	jne    da29 <barriered_work_ingest+0x3a9>
    d8ea:	48 8b 07             	mov    (%rdi),%rax
    d8ed:	48 8d 78 08          	lea    0x8(%rax),%rdi
    d8f1:	48 89 fa             	mov    %rdi,%rdx
    d8f4:	48 c1 ea 03          	shr    $0x3,%rdx
    d8f8:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    d8ff:	0f 85 59 01 00 00    	jne    da5e <barriered_work_ingest+0x3de>
    d905:	48 03 68 08          	add    0x8(%rax),%rbp
    d909:	48 8d bd 94 00 00 00 	lea    0x94(%rbp),%rdi
    d910:	48 89 f8             	mov    %rdi,%rax
    d913:	48 c1 e8 03          	shr    $0x3,%rax
    d917:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    d91e:	48 89 f8             	mov    %rdi,%rax
    d921:	83 e0 07             	and    $0x7,%eax
    d924:	83 c0 03             	add    $0x3,%eax
    d927:	38 d0                	cmp    %dl,%al
    d929:	7c 08                	jl     d933 <barriered_work_ingest+0x2b3>
    d92b:	84 d2                	test   %dl,%dl
    d92d:	0f 85 26 01 00 00    	jne    da59 <barriered_work_ingest+0x3d9>
    d933:	48 8d bd 90 00 00 00 	lea    0x90(%rbp),%rdi
    d93a:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    d940:	48 89 fa             	mov    %rdi,%rdx
    d943:	48 c1 ea 03          	shr    $0x3,%rdx
    d947:	83 c0 01             	add    $0x1,%eax
    d94a:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    d951:	84 d2                	test   %dl,%dl
    d953:	74 09                	je     d95e <barriered_work_ingest+0x2de>
    d955:	80 fa 03             	cmp    $0x3,%dl
    d958:	0f 8e f6 00 00 00    	jle    da54 <barriered_work_ingest+0x3d4>
    d95e:	99                   	cltd
        data->thread->buffers[b]->buffer[x].available = 0;
    d95f:	48 8d bd 80 00 00 00 	lea    0x80(%rbp),%rdi
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    d966:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
        data->thread->buffers[b]->buffer[x].available = 0;
    d96c:	48 89 f8             	mov    %rdi,%rax
    d96f:	48 c1 e8 03          	shr    $0x3,%rax
    d973:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    d97a:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        data->thread->buffers[b]->buffer[x].available = 0;
    d980:	84 c0                	test   %al,%al
    d982:	74 08                	je     d98c <barriered_work_ingest+0x30c>
    d984:	3c 03                	cmp    $0x3,%al
    d986:	0f 8e c3 00 00 00    	jle    da4f <barriered_work_ingest+0x3cf>
    d98c:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        asm volatile ("sfence" ::: "memory");
    d996:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    d999:	4d 8b 96 28 01 00 00 	mov    0x128(%r14),%r10
    d9a0:	49 8d 7a 50          	lea    0x50(%r10),%rdi
    d9a4:	48 89 f8             	mov    %rdi,%rax
    d9a7:	48 c1 e8 03          	shr    $0x3,%rax
    d9ab:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d9b2:	0f 85 92 00 00 00    	jne    da4a <barriered_work_ingest+0x3ca>
    d9b8:	4d 8b 5a 50          	mov    0x50(%r10),%r11
    d9bc:	4b 8d 3c 3b          	lea    (%r11,%r15,1),%rdi
    d9c0:	48 89 f8             	mov    %rdi,%rax
    d9c3:	48 c1 e8 03          	shr    $0x3,%rax
    d9c7:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    d9ce:	75 75                	jne    da45 <barriered_work_ingest+0x3c5>
    d9d0:	48 8b 3f             	mov    (%rdi),%rdi
    d9d3:	48 89 f8             	mov    %rdi,%rax
    d9d6:	48 c1 e8 03          	shr    $0x3,%rax
    d9da:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    d9e1:	84 c0                	test   %al,%al
    d9e3:	74 04                	je     d9e9 <barriered_work_ingest+0x369>
    d9e5:	3c 03                	cmp    $0x3,%al
    d9e7:	7e 57                	jle    da40 <barriered_work_ingest+0x3c0>
    d9e9:	8b 37                	mov    (%rdi),%esi
    d9eb:	48 83 c3 01          	add    $0x1,%rbx
    d9ef:	39 de                	cmp    %ebx,%esi
    d9f1:	0f 8e ce fd ff ff    	jle    d7c5 <barriered_work_ingest+0x145>
    d9f7:	4c 8d 4f 08          	lea    0x8(%rdi),%r9
    d9fb:	e9 70 fd ff ff       	jmp    d770 <barriered_work_ingest+0xf0>
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    da00:	4c 89 cf             	mov    %r9,%rdi
    da03:	e8 d8 6a ff ff       	call   44e0 <__asan_report_load8@plt>
    da08:	48 89 cf             	mov    %rcx,%rdi
    da0b:	e8 40 6b ff ff       	call   4550 <__asan_report_load4@plt>
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    da10:	e8 cb 6a ff ff       	call   44e0 <__asan_report_load8@plt>
        data->ingest_count++;
    da15:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    da1a:	e8 c1 6a ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    da1f:	e8 2c 6b ff ff       	call   4550 <__asan_report_load4@plt>
    da24:	e8 b7 6a ff ff       	call   44e0 <__asan_report_load8@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    da29:	e8 b2 6a ff ff       	call   44e0 <__asan_report_load8@plt>
    da2e:	e8 ad 6a ff ff       	call   44e0 <__asan_report_load8@plt>
    da33:	4c 89 e7             	mov    %r12,%rdi
    da36:	e8 a5 6a ff ff       	call   44e0 <__asan_report_load8@plt>
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    da3b:	e8 10 6b ff ff       	call   4550 <__asan_report_load4@plt>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    da40:	e8 0b 6b ff ff       	call   4550 <__asan_report_load4@plt>
    da45:	e8 96 6a ff ff       	call   44e0 <__asan_report_load8@plt>
    da4a:	e8 91 6a ff ff       	call   44e0 <__asan_report_load8@plt>
        data->thread->buffers[b]->buffer[x].available = 0;
    da4f:	e8 6c 6c ff ff       	call   46c0 <__asan_report_store4@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    da54:	e8 f7 6a ff ff       	call   4550 <__asan_report_load4@plt>
    da59:	e8 f2 6a ff ff       	call   4550 <__asan_report_load4@plt>
    da5e:	e8 7d 6a ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    da63:	e8 78 6a ff ff       	call   44e0 <__asan_report_load8@plt>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    da68:	e8 e3 6a ff ff       	call   4550 <__asan_report_load4@plt>
    da6d:	e8 de 6a ff ff       	call   4550 <__asan_report_load4@plt>
    da72:	4c 89 e7             	mov    %r12,%rdi
    da75:	e8 66 6a ff ff       	call   44e0 <__asan_report_load8@plt>
    da7a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

000000000000da80 <barriered_thread>:
void* barriered_thread(void *arg) {
    da80:	f3 0f 1e fa          	endbr64
    da84:	41 57                	push   %r15
    da86:	48 8d 47 44          	lea    0x44(%rdi),%rax
    da8a:	41 56                	push   %r14
    da8c:	41 55                	push   %r13
  int t = 0;
    da8e:	45 31 ed             	xor    %r13d,%r13d
void* barriered_thread(void *arg) {
    da91:	41 54                	push   %r12
    da93:	55                   	push   %rbp
    da94:	53                   	push   %rbx
    da95:	48 89 fb             	mov    %rdi,%rbx
    da98:	48 83 ec 48          	sub    $0x48,%rsp
    da9c:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
  while (data->running == 1) {
    daa1:	83 e0 07             	and    $0x7,%eax
    daa4:	83 c0 03             	add    $0x3,%eax
  int waiting = 0;
    daa7:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
  while (data->running == 1) {
    daaf:	88 44 24 3f          	mov    %al,0x3f(%rsp)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    dab3:	48 8d 47 04          	lea    0x4(%rdi),%rax
    dab7:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    dabc:	83 e0 07             	and    $0x7,%eax
    dabf:	83 c0 03             	add    $0x3,%eax
    dac2:	88 44 24 3e          	mov    %al,0x3e(%rsp)
  while (data->running == 1) {
    dac6:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    dacb:	48 c1 e8 03          	shr    $0x3,%rax
    dacf:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    dad6:	38 44 24 3f          	cmp    %al,0x3f(%rsp)
    dada:	7c 08                	jl     dae4 <barriered_thread+0x64>
    dadc:	84 c0                	test   %al,%al
    dade:	0f 85 3e 09 00 00    	jne    e422 <barriered_thread+0x9a2>
    dae4:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    dae8:	0f 85 5a 06 00 00    	jne    e148 <barriered_thread+0x6c8>
    if (t >= data->task_count) {
    daee:	4c 8d 7b 40          	lea    0x40(%rbx),%r15
    daf2:	4c 89 f8             	mov    %r15,%rax
    daf5:	48 c1 e8 03          	shr    $0x3,%rax
    daf9:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    db00:	84 c0                	test   %al,%al
    db02:	74 08                	je     db0c <barriered_thread+0x8c>
    db04:	3c 03                	cmp    $0x3,%al
    db06:	0f 8e 0e 09 00 00    	jle    e41a <barriered_thread+0x99a>
    db0c:	8b 53 40             	mov    0x40(%rbx),%edx
    db0f:	90                   	nop
    db10:	41 39 d5             	cmp    %edx,%r13d
    db13:	0f 8d 57 07 00 00    	jge    e270 <barriered_thread+0x7f0>
    db19:	48 8d 43 38          	lea    0x38(%rbx),%rax
    db1d:	4d 63 e5             	movslq %r13d,%r12
      if (data->tasks[t].available == 1) {
    db20:	48 89 c5             	mov    %rax,%rbp
    db23:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    db28:	49 c1 e4 09          	shl    $0x9,%r12
    db2c:	48 c1 ed 03          	shr    $0x3,%rbp
    db30:	e9 b1 00 00 00       	jmp    dbe6 <barriered_thread+0x166>
    db35:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    db38:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    db3c:	48 89 f8             	mov    %rdi,%rax
    db3f:	48 c1 e8 03          	shr    $0x3,%rax
    db43:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    db4a:	0f 85 47 08 00 00    	jne    e397 <barriered_thread+0x917>
    db50:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    db55:	48 8b 53 18          	mov    0x18(%rbx),%rdx
    db59:	48 c1 e8 03          	shr    $0x3,%rax
    db5d:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    db64:	38 44 24 3e          	cmp    %al,0x3e(%rsp)
    db68:	7c 08                	jl     db72 <barriered_thread+0xf2>
    db6a:	84 c0                	test   %al,%al
    db6c:	0f 85 2a 08 00 00    	jne    e39c <barriered_thread+0x91c>
    db72:	48 63 43 04          	movslq 0x4(%rbx),%rax
    db76:	48 8d 3c c2          	lea    (%rdx,%rax,8),%rdi
    db7a:	48 89 f8             	mov    %rdi,%rax
    db7d:	48 c1 e8 03          	shr    $0x3,%rax
    db81:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    db88:	0f 85 18 08 00 00    	jne    e3a6 <barriered_thread+0x926>
    db8e:	48 8b 07             	mov    (%rdi),%rax
    db91:	48 8d 78 38          	lea    0x38(%rax),%rdi
    db95:	48 89 fa             	mov    %rdi,%rdx
    db98:	48 c1 ea 03          	shr    $0x3,%rdx
    db9c:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    dba3:	0f 85 e9 07 00 00    	jne    e392 <barriered_thread+0x912>
    dba9:	48 8b 78 38          	mov    0x38(%rax),%rdi
    dbad:	4c 01 e7             	add    %r12,%rdi
    dbb0:	e8 cb fa ff ff       	call   d680 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    dbb5:	4c 89 f8             	mov    %r15,%rax
    dbb8:	41 83 c5 01          	add    $0x1,%r13d
    dbbc:	48 c1 e8 03          	shr    $0x3,%rax
    dbc0:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    dbc7:	84 c0                	test   %al,%al
    dbc9:	74 08                	je     dbd3 <barriered_thread+0x153>
    dbcb:	3c 03                	cmp    $0x3,%al
    dbcd:	0f 8e a8 07 00 00    	jle    e37b <barriered_thread+0x8fb>
    dbd3:	8b 53 40             	mov    0x40(%rbx),%edx
    dbd6:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    dbdd:	44 39 ea             	cmp    %r13d,%edx
    dbe0:	0f 8e 3a 05 00 00    	jle    e120 <barriered_thread+0x6a0>
      if (data->tasks[t].available == 1) {
    dbe6:	80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rbp)
    dbed:	0f 85 90 07 00 00    	jne    e383 <barriered_thread+0x903>
    dbf3:	48 8b 4b 38          	mov    0x38(%rbx),%rcx
    dbf7:	4c 01 e1             	add    %r12,%rcx
    dbfa:	48 8d b9 44 01 00 00 	lea    0x144(%rcx),%rdi
    dc01:	48 89 f8             	mov    %rdi,%rax
    dc04:	48 c1 e8 03          	shr    $0x3,%rax
    dc08:	0f b6 b0 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%esi
    dc0f:	48 89 f8             	mov    %rdi,%rax
    dc12:	83 e0 07             	and    $0x7,%eax
    dc15:	83 c0 03             	add    $0x3,%eax
    dc18:	40 38 f0             	cmp    %sil,%al
    dc1b:	7c 09                	jl     dc26 <barriered_thread+0x1a6>
    dc1d:	40 84 f6             	test   %sil,%sil
    dc20:	0f 85 67 07 00 00    	jne    e38d <barriered_thread+0x90d>
    dc26:	83 b9 44 01 00 00 01 	cmpl   $0x1,0x144(%rcx)
    dc2d:	0f 85 05 ff ff ff    	jne    db38 <barriered_thread+0xb8>
          previous = t - 1;
    dc33:	41 8d 45 ff          	lea    -0x1(%r13),%eax
    dc37:	83 ea 01             	sub    $0x1,%edx
    dc3a:	45 85 ed             	test   %r13d,%r13d
    dc3d:	0f 4f d0             	cmovg  %eax,%edx
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    dc40:	48 8d 43 28          	lea    0x28(%rbx),%rax
    dc44:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    dc49:	48 c1 e8 03          	shr    $0x3,%rax
    dc4d:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    dc54:	84 c0                	test   %al,%al
    dc56:	74 08                	je     dc60 <barriered_thread+0x1e0>
    dc58:	3c 03                	cmp    $0x3,%al
    dc5a:	0f 8e 4b 07 00 00    	jle    e3ab <barriered_thread+0x92b>
    dc60:	8b 43 28             	mov    0x28(%rbx),%eax
    dc63:	85 c0                	test   %eax,%eax
    dc65:	0f 8e 45 05 00 00    	jle    e1b0 <barriered_thread+0x730>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    dc6b:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    dc6f:	48 89 fe             	mov    %rdi,%rsi
    dc72:	48 c1 ee 03          	shr    $0x3,%rsi
    dc76:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    dc7d:	0f 85 b5 07 00 00    	jne    e438 <barriered_thread+0x9b8>
    dc83:	4c 8d 81 80 00 00 00 	lea    0x80(%rcx),%r8
    dc8a:	48 63 d2             	movslq %edx,%rdx
    dc8d:	48 8b 7b 18          	mov    0x18(%rbx),%rdi
    dc91:	4c 89 c6             	mov    %r8,%rsi
    dc94:	48 c1 e2 09          	shl    $0x9,%rdx
    dc98:	48 c1 ee 03          	shr    $0x3,%rsi
    dc9c:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    dca3:	40 84 f6             	test   %sil,%sil
    dca6:	74 0a                	je     dcb2 <barriered_thread+0x232>
    dca8:	40 80 fe 03          	cmp    $0x3,%sil
    dcac:	0f 8e 7e 07 00 00    	jle    e430 <barriered_thread+0x9b0>
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    dcb2:	4c 8d 81 00 01 00 00 	lea    0x100(%rcx),%r8
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    dcb9:	44 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    dcc0:	4c 89 c6             	mov    %r8,%rsi
    dcc3:	48 c1 ee 03          	shr    $0x3,%rsi
    dcc7:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    dcce:	40 84 f6             	test   %sil,%sil
    dcd1:	74 0a                	je     dcdd <barriered_thread+0x25d>
    dcd3:	40 80 fe 03          	cmp    $0x3,%sil
    dcd7:	0f 8e 9b 07 00 00    	jle    e478 <barriered_thread+0x9f8>
        int arrived = 0; 
    dcdd:	44 89 6c 24 18       	mov    %r13d,0x18(%rsp)
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    dce2:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    dce9:	48 63 c8             	movslq %eax,%rcx
        int prearrive = 0; 
    dcec:	45 31 d2             	xor    %r10d,%r10d
    dcef:	48 8d 34 cf          	lea    (%rdi,%rcx,8),%rsi
        int arrived = 0; 
    dcf3:	45 31 f6             	xor    %r14d,%r14d
    dcf6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    dd00:	48 89 f9             	mov    %rdi,%rcx
    dd03:	48 c1 e9 03          	shr    $0x3,%rcx
    dd07:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    dd0e:	0f 85 62 06 00 00    	jne    e376 <barriered_thread+0x8f6>
    dd14:	4c 8b 1f             	mov    (%rdi),%r11
    dd17:	49 8d 4b 38          	lea    0x38(%r11),%rcx
    dd1b:	49 89 cd             	mov    %rcx,%r13
    dd1e:	49 c1 ed 03          	shr    $0x3,%r13
    dd22:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    dd2a:	0f 85 3e 06 00 00    	jne    e36e <barriered_thread+0x8ee>
    dd30:	49 8b 4b 38          	mov    0x38(%r11),%rcx
    dd34:	48 01 d1             	add    %rdx,%rcx
    dd37:	4c 8d 99 80 00 00 00 	lea    0x80(%rcx),%r11
    dd3e:	4d 89 dd             	mov    %r11,%r13
    dd41:	49 c1 ed 03          	shr    $0x3,%r13
    dd45:	45 0f b6 ad 00 80 ff 7f 	movzbl 0x7fff8000(%r13),%r13d
    dd4d:	45 84 ed             	test   %r13b,%r13b
    dd50:	74 0a                	je     dd5c <barriered_thread+0x2dc>
    dd52:	41 80 fd 03          	cmp    $0x3,%r13b
    dd56:	0f 8e 0a 06 00 00    	jle    e366 <barriered_thread+0x8e6>
    dd5c:	44 39 89 80 00 00 00 	cmp    %r9d,0x80(%rcx)
    dd63:	75 04                	jne    dd69 <barriered_thread+0x2e9>
            arrived++;
    dd65:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    dd69:	4c 8d 99 00 01 00 00 	lea    0x100(%rcx),%r11
    dd70:	4d 89 dd             	mov    %r11,%r13
    dd73:	49 c1 ed 03          	shr    $0x3,%r13
    dd77:	45 0f b6 ad 00 80 ff 7f 	movzbl 0x7fff8000(%r13),%r13d
    dd7f:	45 84 ed             	test   %r13b,%r13b
    dd82:	74 0a                	je     dd8e <barriered_thread+0x30e>
    dd84:	41 80 fd 03          	cmp    $0x3,%r13b
    dd88:	0f 8e d0 05 00 00    	jle    e35e <barriered_thread+0x8de>
    dd8e:	44 39 81 00 01 00 00 	cmp    %r8d,0x100(%rcx)
    dd95:	75 04                	jne    dd9b <barriered_thread+0x31b>
            prearrive++;
    dd97:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    dd9b:	48 83 c7 08          	add    $0x8,%rdi
    dd9f:	48 39 fe             	cmp    %rdi,%rsi
    dda2:	0f 85 58 ff ff ff    	jne    dd00 <barriered_thread+0x280>
        if (prearrive == 0 || prearrive == data->thread_count) {
    dda8:	44 8b 6c 24 18       	mov    0x18(%rsp),%r13d
    ddad:	45 85 d2             	test   %r10d,%r10d
    ddb0:	0f 84 32 02 00 00    	je     dfe8 <barriered_thread+0x568>
    ddb6:	41 39 c2             	cmp    %eax,%r10d
    ddb9:	0f 84 29 02 00 00    	je     dfe8 <barriered_thread+0x568>
        if (arrived == 0 || arrived == data->thread_count) {
    ddbf:	45 85 f6             	test   %r14d,%r14d
    ddc2:	74 26                	je     ddea <barriered_thread+0x36a>
    ddc4:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    ddc9:	48 c1 e8 03          	shr    $0x3,%rax
    ddcd:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    ddd4:	84 c0                	test   %al,%al
    ddd6:	74 08                	je     dde0 <barriered_thread+0x360>
    ddd8:	3c 03                	cmp    $0x3,%al
    ddda:	0f 8e 68 06 00 00    	jle    e448 <barriered_thread+0x9c8>
    dde0:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    dde4:	0f 85 b9 04 00 00    	jne    e2a3 <barriered_thread+0x823>
          data->tasks[t].prearrive++;
    ddea:	80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rbp)
    ddf1:	0f 85 d2 05 00 00    	jne    e3c9 <barriered_thread+0x949>
    ddf7:	48 8b 43 38          	mov    0x38(%rbx),%rax
    ddfb:	4c 01 e0             	add    %r12,%rax
    ddfe:	48 8d b8 00 01 00 00 	lea    0x100(%rax),%rdi
    de05:	48 89 fa             	mov    %rdi,%rdx
    de08:	48 c1 ea 03          	shr    $0x3,%rdx
    de0c:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    de13:	84 d2                	test   %dl,%dl
    de15:	74 09                	je     de20 <barriered_thread+0x3a0>
    de17:	80 fa 03             	cmp    $0x3,%dl
    de1a:	0f 8e de 05 00 00    	jle    e3fe <barriered_thread+0x97e>
    de20:	83 80 00 01 00 00 01 	addl   $0x1,0x100(%rax)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    de27:	45 85 ed             	test   %r13d,%r13d
    de2a:	75 4a                	jne    de76 <barriered_thread+0x3f6>
    de2c:	48 8d bb 80 00 00 00 	lea    0x80(%rbx),%rdi
    de33:	48 89 fa             	mov    %rdi,%rdx
    de36:	48 c1 ea 03          	shr    $0x3,%rdx
    de3a:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    de41:	0f 85 1a 06 00 00    	jne    e461 <barriered_thread+0x9e1>
    de47:	48 8d bb 88 00 00 00 	lea    0x88(%rbx),%rdi
    de4e:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    de55:	48 89 fa             	mov    %rdi,%rdx
    de58:	48 c1 ea 03          	shr    $0x3,%rdx
    de5c:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    de63:	0f 85 f3 05 00 00    	jne    e45c <barriered_thread+0x9dc>
    de69:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    de70:	0f 8c ea 02 00 00    	jl     e160 <barriered_thread+0x6e0>
          data->tasks[t].available = 0;
    de76:	48 8d b8 44 01 00 00 	lea    0x144(%rax),%rdi
    de7d:	48 89 fa             	mov    %rdi,%rdx
    de80:	48 c1 ea 03          	shr    $0x3,%rdx
    de84:	0f b6 8a 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%ecx
    de8b:	48 89 fa             	mov    %rdi,%rdx
    de8e:	83 e2 07             	and    $0x7,%edx
    de91:	83 c2 03             	add    $0x3,%edx
    de94:	38 ca                	cmp    %cl,%dl
    de96:	7c 08                	jl     dea0 <barriered_thread+0x420>
    de98:	84 c9                	test   %cl,%cl
    de9a:	0f 85 38 05 00 00    	jne    e3d8 <barriered_thread+0x958>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    dea0:	48 8d b8 18 01 00 00 	lea    0x118(%rax),%rdi
          data->tasks[t].available = 0;
    dea7:	c7 80 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rax)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    deb1:	48 89 fa             	mov    %rdi,%rdx
    deb4:	48 c1 ea 03          	shr    $0x3,%rdx
    deb8:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    debf:	0f 85 0e 05 00 00    	jne    e3d3 <barriered_thread+0x953>
    dec5:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    dec9:	48 8b 90 18 01 00 00 	mov    0x118(%rax),%rdx
    ded0:	48 89 f8             	mov    %rdi,%rax
    ded3:	48 c1 e8 03          	shr    $0x3,%rax
    ded7:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    dede:	0f 85 e0 04 00 00    	jne    e3c4 <barriered_thread+0x944>
    dee4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    dee9:	48 8b 4b 18          	mov    0x18(%rbx),%rcx
    deed:	48 c1 e8 03          	shr    $0x3,%rax
    def1:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    def8:	38 44 24 3e          	cmp    %al,0x3e(%rsp)
    defc:	7c 08                	jl     df06 <barriered_thread+0x486>
    defe:	84 c0                	test   %al,%al
    df00:	0f 85 b4 04 00 00    	jne    e3ba <barriered_thread+0x93a>
    df06:	48 63 43 04          	movslq 0x4(%rbx),%rax
    df0a:	48 8d 3c c1          	lea    (%rcx,%rax,8),%rdi
    df0e:	48 89 f8             	mov    %rdi,%rax
    df11:	48 c1 e8 03          	shr    $0x3,%rax
    df15:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    df1c:	0f 85 93 04 00 00    	jne    e3b5 <barriered_thread+0x935>
    df22:	48 8b 07             	mov    (%rdi),%rax
    df25:	48 8d 78 38          	lea    0x38(%rax),%rdi
    df29:	48 89 f9             	mov    %rdi,%rcx
    df2c:	48 c1 e9 03          	shr    $0x3,%rcx
    df30:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    df37:	0f 85 bc 04 00 00    	jne    e3f9 <barriered_thread+0x979>
    df3d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    df41:	4c 01 e7             	add    %r12,%rdi
    df44:	ff d2                	call   *%rdx
          data->tasks[t].arrived++;
    df46:	80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rbp)
    df4d:	0f 85 9c 04 00 00    	jne    e3ef <barriered_thread+0x96f>
    df53:	48 8b 43 38          	mov    0x38(%rbx),%rax
    df57:	4c 01 e0             	add    %r12,%rax
    df5a:	48 8d b8 80 00 00 00 	lea    0x80(%rax),%rdi
    df61:	48 89 fa             	mov    %rdi,%rdx
    df64:	48 c1 ea 03          	shr    $0x3,%rdx
    df68:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    df6f:	84 d2                	test   %dl,%dl
    df71:	74 09                	je     df7c <barriered_thread+0x4fc>
    df73:	80 fa 03             	cmp    $0x3,%dl
    df76:	0f 8e 6e 04 00 00    	jle    e3ea <barriered_thread+0x96a>
          data->iteration_count++;
    df7c:	48 8d 7b 78          	lea    0x78(%rbx),%rdi
          data->tasks[t].arrived++;
    df80:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          data->iteration_count++;
    df87:	48 89 f8             	mov    %rdi,%rax
    df8a:	48 c1 e8 03          	shr    $0x3,%rax
    df8e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    df95:	0f 85 4a 04 00 00    	jne    e3e5 <barriered_thread+0x965>
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    df9b:	4c 89 f8             	mov    %r15,%rax
          data->iteration_count++;
    df9e:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    dfa3:	48 c1 e8 03          	shr    $0x3,%rax
    dfa7:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    dfae:	84 c0                	test   %al,%al
    dfb0:	74 08                	je     dfba <barriered_thread+0x53a>
    dfb2:	3c 03                	cmp    $0x3,%al
    dfb4:	0f 8e 23 04 00 00    	jle    e3dd <barriered_thread+0x95d>
    dfba:	8b 43 40             	mov    0x40(%rbx),%eax
    dfbd:	83 e8 01             	sub    $0x1,%eax
    dfc0:	44 39 e8             	cmp    %r13d,%eax
    dfc3:	74 3b                	je     e000 <barriered_thread+0x580>
          asm volatile ("sfence" ::: "memory");
    dfc5:	0f ae f8             	sfence
          if (waiting == 0) {
    dfc8:	8b 44 24 10          	mov    0x10(%rsp),%eax
    dfcc:	85 c0                	test   %eax,%eax
    dfce:	0f 84 cc 00 00 00    	je     e0a0 <barriered_thread+0x620>
        int arrived = 0; 
    dfd4:	c7 44 24 10 01 00 00 00 	movl   $0x1,0x10(%rsp)
    dfdc:	e9 d4 fb ff ff       	jmp    dbb5 <barriered_thread+0x135>
    dfe1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          if (waiting == 1) {
    dfe8:	83 7c 24 10 01       	cmpl   $0x1,0x10(%rsp)
    dfed:	0f 84 cd 01 00 00    	je     e1c0 <barriered_thread+0x740>
        int arrived = 0; 
    dff3:	c7 44 24 10 00 00 00 00 	movl   $0x0,0x10(%rsp)
    dffb:	e9 bf fd ff ff       	jmp    ddbf <barriered_thread+0x33f>
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    e000:	48 8d 93 80 00 00 00 	lea    0x80(%rbx),%rdx
    e007:	49 89 d6             	mov    %rdx,%r14
    e00a:	49 c1 ee 03          	shr    $0x3,%r14
    e00e:	41 80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r14)
    e016:	0f 85 79 04 00 00    	jne    e495 <barriered_thread+0xa15>
    e01c:	48 8d bb 88 00 00 00 	lea    0x88(%rbx),%rdi
    e023:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    e02a:	48 89 f8             	mov    %rdi,%rax
    e02d:	48 c1 e8 03          	shr    $0x3,%rax
    e031:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e038:	0f 85 52 04 00 00    	jne    e490 <barriered_thread+0xa10>
    e03e:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    e045:	0f 8d 7a ff ff ff    	jge    dfc5 <barriered_thread+0x545>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    e04b:	48 8d 7b 70          	lea    0x70(%rbx),%rdi
    e04f:	48 89 f8             	mov    %rdi,%rax
    e052:	48 c1 e8 03          	shr    $0x3,%rax
    e056:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e05d:	0f 85 b2 03 00 00    	jne    e415 <barriered_thread+0x995>
    e063:	48 c1 e6 04          	shl    $0x4,%rsi
    e067:	bf 04 00 00 00       	mov    $0x4,%edi
    e06c:	48 03 73 70          	add    0x70(%rbx),%rsi
    e070:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    e075:	e8 06 64 ff ff       	call   4480 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    e07a:	41 80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r14)
    e082:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    e087:	0f 85 80 03 00 00    	jne    e40d <barriered_thread+0x98d>
    e08d:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    e095:	e9 2b ff ff ff       	jmp    dfc5 <barriered_thread+0x545>
    e09a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    e0a0:	48 8d bb 90 00 00 00 	lea    0x90(%rbx),%rdi
    e0a7:	48 89 f8             	mov    %rdi,%rax
    e0aa:	48 c1 e8 03          	shr    $0x3,%rax
    e0ae:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e0b5:	0f 85 4d 03 00 00    	jne    e408 <barriered_thread+0x988>
    e0bb:	48 8d bb 98 00 00 00 	lea    0x98(%rbx),%rdi
    e0c2:	48 8b 93 90 00 00 00 	mov    0x90(%rbx),%rdx
    e0c9:	48 89 f8             	mov    %rdi,%rax
    e0cc:	48 c1 e8 03          	shr    $0x3,%rax
    e0d0:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e0d7:	0f 85 26 03 00 00    	jne    e403 <barriered_thread+0x983>
    e0dd:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    e0e4:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    e0e8:	48 8d 34 c2          	lea    (%rdx,%rax,8),%rsi
    e0ec:	48 8d 7e 20          	lea    0x20(%rsi),%rdi
    e0f0:	48 89 f8             	mov    %rdi,%rax
    e0f3:	48 c1 e8 03          	shr    $0x3,%rax
    e0f7:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e0fe:	84 c0                	test   %al,%al
    e100:	74 08                	je     e10a <barriered_thread+0x68a>
    e102:	3c 03                	cmp    $0x3,%al
    e104:	0f 8e c8 03 00 00    	jle    e4d2 <barriered_thread+0xa52>
    e10a:	44 89 6e 20          	mov    %r13d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    e10e:	bf 04 00 00 00       	mov    $0x4,%edi
    e113:	e8 68 63 ff ff       	call   4480 <clock_gettime@plt>
            waiting = 1;
    e118:	e9 b7 fe ff ff       	jmp    dfd4 <barriered_thread+0x554>
    e11d:	0f 1f 00             	nopl   (%rax)
  while (data->running == 1) {
    e120:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    e125:	48 c1 e8 03          	shr    $0x3,%rax
    e129:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e130:	38 44 24 3f          	cmp    %al,0x3f(%rsp)
    e134:	7c 08                	jl     e13e <barriered_thread+0x6be>
    e136:	84 c0                	test   %al,%al
    e138:	0f 85 8a 03 00 00    	jne    e4c8 <barriered_thread+0xa48>
    e13e:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    e142:	0f 84 c8 f9 ff ff    	je     db10 <barriered_thread+0x90>
}
    e148:	48 83 c4 48          	add    $0x48,%rsp
    e14c:	31 c0                	xor    %eax,%eax
    e14e:	5b                   	pop    %rbx
    e14f:	5d                   	pop    %rbp
    e150:	41 5c                	pop    %r12
    e152:	41 5d                	pop    %r13
    e154:	41 5e                	pop    %r14
    e156:	41 5f                	pop    %r15
    e158:	c3                   	ret
    e159:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    e160:	48 8d 7b 68          	lea    0x68(%rbx),%rdi
    e164:	48 89 f8             	mov    %rdi,%rax
    e167:	48 c1 e8 03          	shr    $0x3,%rax
    e16b:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e172:	0f 85 4b 03 00 00    	jne    e4c3 <barriered_thread+0xa43>
    e178:	48 c1 e6 04          	shl    $0x4,%rsi
    e17c:	bf 04 00 00 00       	mov    $0x4,%edi
    e181:	48 03 73 68          	add    0x68(%rbx),%rsi
    e185:	e8 f6 62 ff ff       	call   4480 <clock_gettime@plt>
          data->tasks[t].available = 0;
    e18a:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    e18f:	48 c1 e8 03          	shr    $0x3,%rax
    e193:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e19a:	0f 85 19 03 00 00    	jne    e4b9 <barriered_thread+0xa39>
    e1a0:	48 8b 43 38          	mov    0x38(%rbx),%rax
    e1a4:	4c 01 e0             	add    %r12,%rax
    e1a7:	e9 ca fc ff ff       	jmp    de76 <barriered_thread+0x3f6>
    e1ac:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    e1b0:	83 7c 24 10 01       	cmpl   $0x1,0x10(%rsp)
    e1b5:	0f 85 2f fc ff ff    	jne    ddea <barriered_thread+0x36a>
        int arrived = 0; 
    e1bb:	45 31 f6             	xor    %r14d,%r14d
    e1be:	66 90                	xchg   %ax,%ax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    e1c0:	48 8d bb 90 00 00 00 	lea    0x90(%rbx),%rdi
    e1c7:	48 89 f8             	mov    %rdi,%rax
    e1ca:	48 c1 e8 03          	shr    $0x3,%rax
    e1ce:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e1d5:	0f 85 d9 02 00 00    	jne    e4b4 <barriered_thread+0xa34>
    e1db:	48 8d 83 98 00 00 00 	lea    0x98(%rbx),%rax
    e1e2:	48 8b b3 90 00 00 00 	mov    0x90(%rbx),%rsi
    e1e9:	48 89 c1             	mov    %rax,%rcx
    e1ec:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    e1f1:	48 c1 e9 03          	shr    $0x3,%rcx
    e1f5:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    e1fc:	0f 85 aa 02 00 00    	jne    e4ac <barriered_thread+0xa2c>
    e202:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    e209:	bf 04 00 00 00       	mov    $0x4,%edi
    e20e:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    e213:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    e217:	48 8d 74 c6 10       	lea    0x10(%rsi,%rax,8),%rsi
    e21c:	e8 5f 62 ff ff       	call   4480 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    e221:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    e226:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    e22d:	0f 85 6f 02 00 00    	jne    e4a2 <barriered_thread+0xa22>
    e233:	48 8d bb a0 00 00 00 	lea    0xa0(%rbx),%rdi
    e23a:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    e241:	48 89 fa             	mov    %rdi,%rdx
    e244:	48 c1 ea 03          	shr    $0x3,%rdx
    e248:	48 83 c0 01          	add    $0x1,%rax
    e24c:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    e253:	0f 85 44 02 00 00    	jne    e49d <barriered_thread+0xa1d>
    e259:	48 99                	cqto
    e25b:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    e262:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    e269:	e9 85 fd ff ff       	jmp    dff3 <barriered_thread+0x573>
    e26e:	66 90                	xchg   %ax,%ax
    e270:	48 8d bb a8 00 00 00 	lea    0xa8(%rbx),%rdi
      data->cycles++;
    e277:	48 89 f8             	mov    %rdi,%rax
    e27a:	48 c1 e8 03          	shr    $0x3,%rax
    e27e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e285:	0f 85 cc 01 00 00    	jne    e457 <barriered_thread+0x9d7>
    e28b:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    e293:	85 d2                	test   %edx,%edx
    e295:	0f 8e 8a 00 00 00    	jle    e325 <barriered_thread+0x8a5>
    e29b:	45 31 ed             	xor    %r13d,%r13d
    e29e:	e9 76 f8 ff ff       	jmp    db19 <barriered_thread+0x99>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    e2a3:	48 8d 7b 18          	lea    0x18(%rbx),%rdi
    e2a7:	48 89 f8             	mov    %rdi,%rax
    e2aa:	48 c1 e8 03          	shr    $0x3,%rax
    e2ae:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e2b5:	0f 85 97 01 00 00    	jne    e452 <barriered_thread+0x9d2>
    e2bb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    e2c0:	48 8b 53 18          	mov    0x18(%rbx),%rdx
    e2c4:	48 c1 e8 03          	shr    $0x3,%rax
    e2c8:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e2cf:	38 44 24 3e          	cmp    %al,0x3e(%rsp)
    e2d3:	7c 08                	jl     e2dd <barriered_thread+0x85d>
    e2d5:	84 c0                	test   %al,%al
    e2d7:	0f 85 8e 01 00 00    	jne    e46b <barriered_thread+0x9eb>
    e2dd:	48 63 43 04          	movslq 0x4(%rbx),%rax
    e2e1:	48 8d 3c c2          	lea    (%rdx,%rax,8),%rdi
    e2e5:	48 89 f8             	mov    %rdi,%rax
    e2e8:	48 c1 e8 03          	shr    $0x3,%rax
    e2ec:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e2f3:	0f 85 6d 01 00 00    	jne    e466 <barriered_thread+0x9e6>
    e2f9:	48 8b 07             	mov    (%rdi),%rax
    e2fc:	48 8d 78 38          	lea    0x38(%rax),%rdi
    e300:	48 89 fa             	mov    %rdi,%rdx
    e303:	48 c1 ea 03          	shr    $0x3,%rdx
    e307:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    e30e:	0f 85 29 01 00 00    	jne    e43d <barriered_thread+0x9bd>
    e314:	48 8b 78 38          	mov    0x38(%rax),%rdi
    e318:	4c 01 e7             	add    %r12,%rdi
    e31b:	e8 60 f3 ff ff       	call   d680 <barriered_work_ingest>
          break;
    e320:	e9 a1 f7 ff ff       	jmp    dac6 <barriered_thread+0x46>
  while (data->running == 1) {
    e325:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
    e32a:	4c 89 d1             	mov    %r10,%rcx
    e32d:	48 c1 e9 03          	shr    $0x3,%rcx
    e331:	0f b6 b1 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%esi
    e338:	4c 89 d1             	mov    %r10,%rcx
    e33b:	83 e1 07             	and    $0x7,%ecx
    e33e:	83 c1 03             	add    $0x3,%ecx
    e341:	40 38 f1             	cmp    %sil,%cl
    e344:	7c 09                	jl     e34f <barriered_thread+0x8cf>
    e346:	40 84 f6             	test   %sil,%sil
    e349:	0f 85 31 01 00 00    	jne    e480 <barriered_thread+0xa00>
    e34f:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    e353:	0f 84 25 ff ff ff    	je     e27e <barriered_thread+0x7fe>
    e359:	e9 ea fd ff ff       	jmp    e148 <barriered_thread+0x6c8>
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    e35e:	4c 89 df             	mov    %r11,%rdi
    e361:	e8 ea 61 ff ff       	call   4550 <__asan_report_load4@plt>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    e366:	4c 89 df             	mov    %r11,%rdi
    e369:	e8 e2 61 ff ff       	call   4550 <__asan_report_load4@plt>
    e36e:	48 89 cf             	mov    %rcx,%rdi
    e371:	e8 6a 61 ff ff       	call   44e0 <__asan_report_load8@plt>
    e376:	e8 65 61 ff ff       	call   44e0 <__asan_report_load8@plt>
    for (; t < data->task_count; t++) {
    e37b:	4c 89 ff             	mov    %r15,%rdi
    e37e:	e8 cd 61 ff ff       	call   4550 <__asan_report_load4@plt>
      if (data->tasks[t].available == 1) {
    e383:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    e388:	e8 53 61 ff ff       	call   44e0 <__asan_report_load8@plt>
    e38d:	e8 be 61 ff ff       	call   4550 <__asan_report_load4@plt>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    e392:	e8 49 61 ff ff       	call   44e0 <__asan_report_load8@plt>
    e397:	e8 44 61 ff ff       	call   44e0 <__asan_report_load8@plt>
    e39c:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    e3a1:	e8 aa 61 ff ff       	call   4550 <__asan_report_load4@plt>
    e3a6:	e8 35 61 ff ff       	call   44e0 <__asan_report_load8@plt>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    e3ab:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    e3b0:	e8 9b 61 ff ff       	call   4550 <__asan_report_load4@plt>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    e3b5:	e8 26 61 ff ff       	call   44e0 <__asan_report_load8@plt>
    e3ba:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    e3bf:	e8 8c 61 ff ff       	call   4550 <__asan_report_load4@plt>
    e3c4:	e8 17 61 ff ff       	call   44e0 <__asan_report_load8@plt>
          data->tasks[t].prearrive++;
    e3c9:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    e3ce:	e8 0d 61 ff ff       	call   44e0 <__asan_report_load8@plt>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    e3d3:	e8 08 61 ff ff       	call   44e0 <__asan_report_load8@plt>
          data->tasks[t].available = 0;
    e3d8:	e8 e3 62 ff ff       	call   46c0 <__asan_report_store4@plt>
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    e3dd:	4c 89 ff             	mov    %r15,%rdi
    e3e0:	e8 6b 61 ff ff       	call   4550 <__asan_report_load4@plt>
          data->iteration_count++;
    e3e5:	e8 f6 60 ff ff       	call   44e0 <__asan_report_load8@plt>
          data->tasks[t].arrived++;
    e3ea:	e8 61 61 ff ff       	call   4550 <__asan_report_load4@plt>
    e3ef:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    e3f4:	e8 e7 60 ff ff       	call   44e0 <__asan_report_load8@plt>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    e3f9:	e8 e2 60 ff ff       	call   44e0 <__asan_report_load8@plt>
          data->tasks[t].prearrive++;
    e3fe:	e8 4d 61 ff ff       	call   4550 <__asan_report_load4@plt>
            data->task_snapshot[data->task_timestamp_count].task = t;
    e403:	e8 d8 60 ff ff       	call   44e0 <__asan_report_load8@plt>
    e408:	e8 d3 60 ff ff       	call   44e0 <__asan_report_load8@plt>
            data->timestamp_count = data->timestamp_count + 1;
    e40d:	48 89 d7             	mov    %rdx,%rdi
    e410:	e8 cb 60 ff ff       	call   44e0 <__asan_report_load8@plt>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    e415:	e8 c6 60 ff ff       	call   44e0 <__asan_report_load8@plt>
    if (t >= data->task_count) {
    e41a:	4c 89 ff             	mov    %r15,%rdi
    e41d:	e8 2e 61 ff ff       	call   4550 <__asan_report_load4@plt>
  while (data->running == 1) {
    e422:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    e427:	e8 24 61 ff ff       	call   4550 <__asan_report_load4@plt>
    e42c:	0f 1f 40 00          	nopl   0x0(%rax)
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    e430:	4c 89 c7             	mov    %r8,%rdi
    e433:	e8 18 61 ff ff       	call   4550 <__asan_report_load4@plt>
    e438:	e8 a3 60 ff ff       	call   44e0 <__asan_report_load8@plt>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    e43d:	e8 9e 60 ff ff       	call   44e0 <__asan_report_load8@plt>
    e442:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        if (arrived == 0 || arrived == data->thread_count) {
    e448:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    e44d:	e8 fe 60 ff ff       	call   4550 <__asan_report_load4@plt>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    e452:	e8 89 60 ff ff       	call   44e0 <__asan_report_load8@plt>
      data->cycles++;
    e457:	e8 84 60 ff ff       	call   44e0 <__asan_report_load8@plt>
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    e45c:	e8 7f 60 ff ff       	call   44e0 <__asan_report_load8@plt>
    e461:	e8 7a 60 ff ff       	call   44e0 <__asan_report_load8@plt>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    e466:	e8 75 60 ff ff       	call   44e0 <__asan_report_load8@plt>
    e46b:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    e470:	e8 db 60 ff ff       	call   4550 <__asan_report_load4@plt>
    e475:	0f 1f 00             	nopl   (%rax)
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    e478:	4c 89 c7             	mov    %r8,%rdi
    e47b:	e8 d0 60 ff ff       	call   4550 <__asan_report_load4@plt>
  while (data->running == 1) {
    e480:	4c 89 d7             	mov    %r10,%rdi
    e483:	e8 c8 60 ff ff       	call   4550 <__asan_report_load4@plt>
    e488:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    e490:	e8 4b 60 ff ff       	call   44e0 <__asan_report_load8@plt>
    e495:	48 89 d7             	mov    %rdx,%rdi
    e498:	e8 43 60 ff ff       	call   44e0 <__asan_report_load8@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    e49d:	e8 3e 60 ff ff       	call   44e0 <__asan_report_load8@plt>
    e4a2:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    e4a7:	e8 34 60 ff ff       	call   44e0 <__asan_report_load8@plt>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    e4ac:	48 89 c7             	mov    %rax,%rdi
    e4af:	e8 2c 60 ff ff       	call   44e0 <__asan_report_load8@plt>
    e4b4:	e8 27 60 ff ff       	call   44e0 <__asan_report_load8@plt>
          data->tasks[t].available = 0;
    e4b9:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    e4be:	e8 1d 60 ff ff       	call   44e0 <__asan_report_load8@plt>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    e4c3:	e8 18 60 ff ff       	call   44e0 <__asan_report_load8@plt>
  while (data->running == 1) {
    e4c8:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    e4cd:	e8 7e 60 ff ff       	call   4550 <__asan_report_load4@plt>
            data->task_snapshot[data->task_timestamp_count].task = t;
    e4d2:	e8 e9 61 ff ff       	call   46c0 <__asan_report_store4@plt>
    e4d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

000000000000e4e0 <receive>:
int receive(struct BarrierTask *data) {
    e4e0:	f3 0f 1e fa          	endbr64
    e4e4:	41 57                	push   %r15
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    e4e6:	48 8d 87 40 01 00 00 	lea    0x140(%rdi),%rax
int receive(struct BarrierTask *data) {
    e4ed:	48 89 f9             	mov    %rdi,%rcx
    e4f0:	41 56                	push   %r14
    e4f2:	41 55                	push   %r13
    e4f4:	41 54                	push   %r12
    e4f6:	55                   	push   %rbp
    e4f7:	53                   	push   %rbx
    e4f8:	48 83 ec 68          	sub    $0x68,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    e4fc:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    e501:	48 c1 e8 03          	shr    $0x3,%rax
    e505:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e50c:	84 c0                	test   %al,%al
    e50e:	74 08                	je     e518 <receive+0x38>
    e510:	3c 03                	cmp    $0x3,%al
    e512:	0f 8e 59 04 00 00    	jle    e971 <receive+0x491>
    e518:	8b 81 40 01 00 00    	mov    0x140(%rcx),%eax
    e51e:	48 8d 91 70 01 00 00 	lea    0x170(%rcx),%rdx
    e525:	45 31 ff             	xor    %r15d,%r15d
    e528:	45 31 f6             	xor    %r14d,%r14d
    e52b:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    e530:	85 c0                	test   %eax,%eax
    e532:	0f 8e d4 02 00 00    	jle    e80c <receive+0x32c>
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    e538:	48 8d 51 04          	lea    0x4(%rcx),%rdx
      data->sends++;
    e53c:	4c 8d 91 78 01 00 00 	lea    0x178(%rcx),%r10
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    e543:	48 89 54 24 20       	mov    %rdx,0x20(%rsp)
    e548:	83 e2 07             	and    $0x7,%edx
      data->n++;
    e54b:	4c 8d 99 08 01 00 00 	lea    0x108(%rcx),%r11
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    e552:	48 8d 99 30 01 00 00 	lea    0x130(%rcx),%rbx
    e559:	83 c2 03             	add    $0x3,%edx
    e55c:	4c 89 54 24 48       	mov    %r10,0x48(%rsp)
    e561:	49 89 dd             	mov    %rbx,%r13
    e564:	88 54 24 2f          	mov    %dl,0x2f(%rsp)
      data->sends++;
    e568:	4c 89 d2             	mov    %r10,%rdx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    e56b:	49 c1 ed 03          	shr    $0x3,%r13
      data->sends++;
    e56f:	48 c1 ea 03          	shr    $0x3,%rdx
    e573:	4c 89 5c 24 50       	mov    %r11,0x50(%rsp)
    e578:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
      data->n++;
    e57d:	4c 89 da             	mov    %r11,%rdx
    e580:	48 89 5c 24 58       	mov    %rbx,0x58(%rsp)
    e585:	48 c1 ea 03          	shr    $0x3,%rdx
    e589:	48 89 54 24 38       	mov    %rdx,0x38(%rsp)
    e58e:	4c 89 fa             	mov    %r15,%rdx
    e591:	45 89 f7             	mov    %r14d,%r15d
    e594:	0f 1f 40 00          	nopl   0x0(%rax)
    struct Data *me = data->mailboxes[n].lower;
    e598:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    e59d:	48 c1 ee 03          	shr    $0x3,%rsi
    e5a1:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    e5a8:	0f 85 b9 03 00 00    	jne    e967 <receive+0x487>
    e5ae:	4c 8b 89 70 01 00 00 	mov    0x170(%rcx),%r9
    e5b5:	49 01 d1             	add    %rdx,%r9
    e5b8:	4c 89 ce             	mov    %r9,%rsi
    e5bb:	48 c1 ee 03          	shr    $0x3,%rsi
    e5bf:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    e5c6:	0f 85 93 03 00 00    	jne    e95f <receive+0x47f>
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    e5cc:	49 8d 79 20          	lea    0x20(%r9),%rdi
    struct Data *me = data->mailboxes[n].lower;
    e5d0:	4d 8b 01             	mov    (%r9),%r8
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    e5d3:	48 89 fe             	mov    %rdi,%rsi
    e5d6:	48 c1 ee 03          	shr    $0x3,%rsi
    e5da:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    e5e1:	40 84 f6             	test   %sil,%sil
    e5e4:	74 0a                	je     e5f0 <receive+0x110>
    e5e6:	40 80 fe 03          	cmp    $0x3,%sil
    e5ea:	0f 8e 3d 03 00 00    	jle    e92d <receive+0x44d>
    e5f0:	45 8b 51 20          	mov    0x20(%r9),%r10d
    e5f4:	41 83 fa 02          	cmp    $0x2,%r10d
    e5f8:	0f 84 72 02 00 00    	je     e870 <receive+0x390>
    for (int x = 0 ; x < me->messages_count ; x++) {
    e5fe:	49 8d 40 08          	lea    0x8(%r8),%rax
    e602:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    e607:	48 c1 e8 03          	shr    $0x3,%rax
    e60b:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e612:	0f 85 0b 03 00 00    	jne    e923 <receive+0x443>
    e618:	4d 8b 60 08          	mov    0x8(%r8),%r12
    e61c:	4d 85 e4             	test   %r12,%r12
    e61f:	0f 8e 93 01 00 00    	jle    e7b8 <receive+0x2d8>
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    e625:	4c 89 c0             	mov    %r8,%rax
    e628:	48 c1 e8 03          	shr    $0x3,%rax
    e62c:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e633:	0f 85 e2 02 00 00    	jne    e91b <receive+0x43b>
    e639:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    e63e:	49 8b 38             	mov    (%r8),%rdi
    e641:	48 c1 e8 03          	shr    $0x3,%rax
    e645:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e64c:	38 44 24 2f          	cmp    %al,0x2f(%rsp)
    e650:	7c 08                	jl     e65a <receive+0x17a>
    e652:	84 c0                	test   %al,%al
    e654:	0f 85 ec 02 00 00    	jne    e946 <receive+0x466>
      data->sends++;
    e65a:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    e65f:	4c 63 71 04          	movslq 0x4(%rcx),%r14
      data->sends++;
    e663:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e66a:	0f 85 2a 03 00 00    	jne    e99a <receive+0x4ba>
      data->n++;
    e670:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
      data->sends++;
    e675:	4c 8b 99 78 01 00 00 	mov    0x178(%rcx),%r11
      data->n++;
    e67c:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e683:	0f 85 07 03 00 00    	jne    e990 <receive+0x4b0>
      data->mailboxes[n].received++;
    e689:	49 8d 41 18          	lea    0x18(%r9),%rax
      data->n++;
    e68d:	48 8b a9 08 01 00 00 	mov    0x108(%rcx),%rbp
      data->mailboxes[n].received++;
    e694:	48 89 c6             	mov    %rax,%rsi
    e697:	48 c1 ee 03          	shr    $0x3,%rsi
    e69b:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    e6a2:	0f 85 e0 02 00 00    	jne    e988 <receive+0x4a8>
    e6a8:	49 8b 59 18          	mov    0x18(%r9),%rbx
    e6ac:	44 89 54 24 28       	mov    %r10d,0x28(%rsp)
    e6b1:	49 8d 43 01          	lea    0x1(%r11),%rax
      data->n++;
    e6b5:	4c 29 dd             	sub    %r11,%rbp
      data->mailboxes[n].received++;
    e6b8:	4c 89 44 24 10       	mov    %r8,0x10(%rsp)
    e6bd:	4c 29 db             	sub    %r11,%rbx
    e6c0:	eb 21                	jmp    e6e3 <receive+0x203>
    e6c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < me->messages_count ; x++) {
    e6c8:	48 83 c0 01          	add    $0x1,%rax
    e6cc:	48 83 c7 08          	add    $0x8,%rdi
    e6d0:	48 89 c6             	mov    %rax,%rsi
    e6d3:	4c 29 de             	sub    %r11,%rsi
    e6d6:	48 83 ee 01          	sub    $0x1,%rsi
    e6da:	49 39 f4             	cmp    %rsi,%r12
    e6dd:	0f 8e c5 00 00 00    	jle    e7a8 <receive+0x2c8>
      data->n++;
    e6e3:	48 8d 74 05 00       	lea    0x0(%rbp,%rax,1),%rsi
      data->sends++;
    e6e8:	48 89 81 78 01 00 00 	mov    %rax,0x178(%rcx)
      data->n++;
    e6ef:	48 89 b1 08 01 00 00 	mov    %rsi,0x108(%rcx)
      data->mailboxes[n].received++;
    e6f6:	48 8d 34 03          	lea    (%rbx,%rax,1),%rsi
    e6fa:	49 89 71 18          	mov    %rsi,0x18(%r9)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    e6fe:	48 89 fe             	mov    %rdi,%rsi
    e701:	48 c1 ee 03          	shr    $0x3,%rsi
    e705:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    e70c:	0f 85 ea 01 00 00    	jne    e8fc <receive+0x41c>
    e712:	4c 8b 07             	mov    (%rdi),%r8
    e715:	49 8d 70 10          	lea    0x10(%r8),%rsi
    e719:	49 89 f2             	mov    %rsi,%r10
    e71c:	49 c1 ea 03          	shr    $0x3,%r10
    e720:	41 80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r10)
    e728:	0f 85 d3 01 00 00    	jne    e901 <receive+0x421>
    e72e:	4d 39 70 10          	cmp    %r14,0x10(%r8)
    e732:	75 94                	jne    e6c8 <receive+0x1e8>
    e734:	49 8d 70 08          	lea    0x8(%r8),%rsi
    e738:	49 89 f2             	mov    %rsi,%r10
    e73b:	49 c1 ea 03          	shr    $0x3,%r10
    e73f:	41 80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r10)
    e747:	0f 85 c6 01 00 00    	jne    e913 <receive+0x433>
    e74d:	41 0f b6 b5 00 80 ff 7f 	movzbl 0x7fff8000(%r13),%esi
    e755:	4d 8b 40 08          	mov    0x8(%r8),%r8
    e759:	40 84 f6             	test   %sil,%sil
    e75c:	74 0a                	je     e768 <receive+0x288>
    e75e:	40 80 fe 03          	cmp    $0x3,%sil
    e762:	0f 8e a1 01 00 00    	jle    e909 <receive+0x429>
    e768:	48 63 b1 30 01 00 00 	movslq 0x130(%rcx),%rsi
    e76f:	49 39 f0             	cmp    %rsi,%r8
    e772:	0f 85 50 ff ff ff    	jne    e6c8 <receive+0x1e8>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    e778:	bf 01 00 00 00       	mov    $0x1,%edi
    e77d:	b9 01 00 00 00       	mov    $0x1,%ecx
    e782:	ba 01 00 00 00       	mov    $0x1,%edx
    e787:	31 c0                	xor    %eax,%eax
    e789:	48 8d 35 70 36 00 00 	lea    0x3670(%rip),%rsi        # 11e00 <_IO_stdin_used+0xe00>
    e790:	e8 8b 5d ff ff       	call   4520 <__printf_chk@plt>
        exit(1);
    e795:	e8 76 5e ff ff       	call   4610 <__asan_handle_no_return@plt>
    e79a:	bf 01 00 00 00       	mov    $0x1,%edi
    e79f:	e8 6c 5d ff ff       	call   4510 <exit@plt>
    e7a4:	0f 1f 40 00          	nopl   0x0(%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    e7a8:	44 8b 54 24 28       	mov    0x28(%rsp),%r10d
    e7ad:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    e7b2:	41 83 fa 02          	cmp    $0x2,%r10d
    e7b6:	74 68                	je     e820 <receive+0x340>
    me->messages_count = 0;
    e7b8:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    e7bd:	48 c1 e8 03          	shr    $0x3,%rax
    e7c1:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e7c8:	0f 85 6e 01 00 00    	jne    e93c <receive+0x45c>
    e7ce:	49 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%r8)
    asm volatile ("sfence" ::: "memory");
    e7d6:	0f ae f8             	sfence
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    e7d9:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    e7de:	48 c1 e8 03          	shr    $0x3,%rax
    e7e2:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e7e9:	84 c0                	test   %al,%al
    e7eb:	74 08                	je     e7f5 <receive+0x315>
    e7ed:	3c 03                	cmp    $0x3,%al
    e7ef:	0f 8e 3d 01 00 00    	jle    e932 <receive+0x452>
    e7f5:	8b 81 40 01 00 00    	mov    0x140(%rcx),%eax
    e7fb:	41 83 c7 01          	add    $0x1,%r15d
    e7ff:	48 83 c2 28          	add    $0x28,%rdx
    e803:	41 39 c7             	cmp    %eax,%r15d
    e806:	0f 8c 8c fd ff ff    	jl     e598 <receive+0xb8>
}
    e80c:	48 83 c4 68          	add    $0x68,%rsp
    e810:	31 c0                	xor    %eax,%eax
    e812:	5b                   	pop    %rbx
    e813:	5d                   	pop    %rbp
    e814:	41 5c                	pop    %r12
    e816:	41 5d                	pop    %r13
    e818:	41 5e                	pop    %r14
    e81a:	41 5f                	pop    %r15
    e81c:	c3                   	ret
    e81d:	0f 1f 00             	nopl   (%rax)
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    e820:	49 8d 78 18          	lea    0x18(%r8),%rdi
    e824:	48 89 f8             	mov    %rdi,%rax
    e827:	48 c1 e8 03          	shr    $0x3,%rax
    e82b:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e832:	84 c0                	test   %al,%al
    e834:	74 08                	je     e83e <receive+0x35e>
    e836:	3c 03                	cmp    $0x3,%al
    e838:	0f 8e 1c 01 00 00    	jle    e95a <receive+0x47a>
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    e83e:	41 83 78 18 01       	cmpl   $0x1,0x18(%r8)
    e843:	0f 85 6f ff ff ff    	jne    e7b8 <receive+0x2d8>
      me->available = 0;
    e849:	48 89 f8             	mov    %rdi,%rax
    e84c:	48 c1 e8 03          	shr    $0x3,%rax
    e850:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e857:	84 c0                	test   %al,%al
    e859:	74 08                	je     e863 <receive+0x383>
    e85b:	3c 03                	cmp    $0x3,%al
    e85d:	0f 8e f2 00 00 00    	jle    e955 <receive+0x475>
    e863:	41 c7 40 18 00 00 00 00 	movl   $0x0,0x18(%r8)
    e86b:	e9 48 ff ff ff       	jmp    e7b8 <receive+0x2d8>
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    e870:	49 8d 78 18          	lea    0x18(%r8),%rdi
    e874:	48 89 fe             	mov    %rdi,%rsi
    e877:	48 c1 ee 03          	shr    $0x3,%rsi
    e87b:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    e882:	40 84 f6             	test   %sil,%sil
    e885:	74 0a                	je     e891 <receive+0x3b1>
    e887:	40 80 fe 03          	cmp    $0x3,%sil
    e88b:	0f 8e bf 00 00 00    	jle    e950 <receive+0x470>
    e891:	41 8b 70 18          	mov    0x18(%r8),%esi
    e895:	83 fe 01             	cmp    $0x1,%esi
    e898:	74 36                	je     e8d0 <receive+0x3f0>
    else if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 0) {
    e89a:	85 f6                	test   %esi,%esi
    e89c:	0f 84 59 ff ff ff    	je     e7fb <receive+0x31b>
    for (int x = 0 ; x < me->messages_count ; x++) {
    e8a2:	49 8d 40 08          	lea    0x8(%r8),%rax
    e8a6:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    e8ab:	48 c1 e8 03          	shr    $0x3,%rax
    e8af:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e8b6:	0f 84 5c fd ff ff    	je     e618 <receive+0x138>
    e8bc:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    e8c1:	e8 1a 5c ff ff       	call   44e0 <__asan_report_load8@plt>
    e8c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    e8d0:	49 8d 40 08          	lea    0x8(%r8),%rax
    e8d4:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    e8d9:	48 c1 e8 03          	shr    $0x3,%rax
    e8dd:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    e8e4:	0f 85 91 00 00 00    	jne    e97b <receive+0x49b>
    e8ea:	4d 8b 60 08          	mov    0x8(%r8),%r12
    e8ee:	4d 85 e4             	test   %r12,%r12
    e8f1:	0f 8f 2e fd ff ff    	jg     e625 <receive+0x145>
    e8f7:	e9 4d ff ff ff       	jmp    e849 <receive+0x369>
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    e8fc:	e8 df 5b ff ff       	call   44e0 <__asan_report_load8@plt>
    e901:	48 89 f7             	mov    %rsi,%rdi
    e904:	e8 d7 5b ff ff       	call   44e0 <__asan_report_load8@plt>
    e909:	48 8b 7c 24 58       	mov    0x58(%rsp),%rdi
    e90e:	e8 3d 5c ff ff       	call   4550 <__asan_report_load4@plt>
    e913:	48 89 f7             	mov    %rsi,%rdi
    e916:	e8 c5 5b ff ff       	call   44e0 <__asan_report_load8@plt>
    e91b:	4c 89 c7             	mov    %r8,%rdi
    e91e:	e8 bd 5b ff ff       	call   44e0 <__asan_report_load8@plt>
    for (int x = 0 ; x < me->messages_count ; x++) {
    e923:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    e928:	e8 b3 5b ff ff       	call   44e0 <__asan_report_load8@plt>
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    e92d:	e8 1e 5c ff ff       	call   4550 <__asan_report_load4@plt>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    e932:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    e937:	e8 14 5c ff ff       	call   4550 <__asan_report_load4@plt>
    me->messages_count = 0;
    e93c:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    e941:	e8 8a 5d ff ff       	call   46d0 <__asan_report_store8@plt>
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
    e946:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    e94b:	e8 00 5c ff ff       	call   4550 <__asan_report_load4@plt>
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    e950:	e8 fb 5b ff ff       	call   4550 <__asan_report_load4@plt>
      me->available = 0;
    e955:	e8 66 5d ff ff       	call   46c0 <__asan_report_store4@plt>
    if (data->mailboxes[n].kind == MAILBOX_FOREIGN && me->available == 1) {
    e95a:	e8 f1 5b ff ff       	call   4550 <__asan_report_load4@plt>
    struct Data *me = data->mailboxes[n].lower;
    e95f:	4c 89 cf             	mov    %r9,%rdi
    e962:	e8 79 5b ff ff       	call   44e0 <__asan_report_load8@plt>
    e967:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    e96c:	e8 6f 5b ff ff       	call   44e0 <__asan_report_load8@plt>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    e971:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
    e976:	e8 d5 5b ff ff       	call   4550 <__asan_report_load4@plt>
    for (int x = 0 ; x < me->messages_count ; x++) {
    e97b:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    e980:	e8 5b 5b ff ff       	call   44e0 <__asan_report_load8@plt>
    e985:	0f 1f 00             	nopl   (%rax)
      data->mailboxes[n].received++;
    e988:	48 89 c7             	mov    %rax,%rdi
    e98b:	e8 50 5b ff ff       	call   44e0 <__asan_report_load8@plt>
      data->n++;
    e990:	48 8b 7c 24 50       	mov    0x50(%rsp),%rdi
    e995:	e8 46 5b ff ff       	call   44e0 <__asan_report_load8@plt>
      data->sends++;
    e99a:	48 8b 7c 24 48       	mov    0x48(%rsp),%rdi
    e99f:	e8 3c 5b ff ff       	call   44e0 <__asan_report_load8@plt>
    e9a4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    e9af:	90                   	nop

000000000000e9b0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    e9b0:	f3 0f 1e fa          	endbr64
    e9b4:	41 57                	push   %r15
  if (data->thread_index == data->task_index) {
    e9b6:	48 8d 8f 30 01 00 00 	lea    0x130(%rdi),%rcx
int barriered_work(struct BarrierTask *data) {
    e9bd:	41 56                	push   %r14
  if (data->thread_index == data->task_index) {
    e9bf:	48 89 c8             	mov    %rcx,%rax
int barriered_work(struct BarrierTask *data) {
    e9c2:	41 55                	push   %r13
  if (data->thread_index == data->task_index) {
    e9c4:	48 c1 e8 03          	shr    $0x3,%rax
int barriered_work(struct BarrierTask *data) {
    e9c8:	41 54                	push   %r12
    e9ca:	55                   	push   %rbp
    e9cb:	53                   	push   %rbx
    e9cc:	48 89 fb             	mov    %rdi,%rbx
    e9cf:	48 83 ec 48          	sub    $0x48,%rsp
  if (data->thread_index == data->task_index) {
    e9d3:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    e9da:	84 c0                	test   %al,%al
    e9dc:	74 08                	je     e9e6 <barriered_work+0x36>
    e9de:	3c 03                	cmp    $0x3,%al
    e9e0:	0f 8e e3 08 00 00    	jle    f2c9 <barriered_work+0x919>
    e9e6:	4c 8d 7b 04          	lea    0x4(%rbx),%r15
    e9ea:	8b b3 30 01 00 00    	mov    0x130(%rbx),%esi
    e9f0:	4c 89 f8             	mov    %r15,%rax
    e9f3:	48 c1 e8 03          	shr    $0x3,%rax
    e9f7:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    e9fe:	4c 89 f8             	mov    %r15,%rax
    ea01:	83 e0 07             	and    $0x7,%eax
    ea04:	83 c0 03             	add    $0x3,%eax
    ea07:	38 d0                	cmp    %dl,%al
    ea09:	7c 08                	jl     ea13 <barriered_work+0x63>
    ea0b:	84 d2                	test   %dl,%dl
    ea0d:	0f 85 ae 08 00 00    	jne    f2c1 <barriered_work+0x911>
    ea13:	3b 73 04             	cmp    0x4(%rbx),%esi
    ea16:	0f 84 dc 00 00 00    	je     eaf8 <barriered_work+0x148>
    receive(data);
    ea1c:	48 89 df             	mov    %rbx,%rdi
    ea1f:	e8 bc fa ff ff       	call   e4e0 <receive>
    while (data->scheduled == 1) {
    ea24:	48 8d bb 4c 01 00 00 	lea    0x14c(%rbx),%rdi
    ea2b:	48 89 f8             	mov    %rdi,%rax
    ea2e:	48 c1 e8 03          	shr    $0x3,%rax
    ea32:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    ea39:	48 89 f8             	mov    %rdi,%rax
    ea3c:	83 e0 07             	and    $0x7,%eax
    ea3f:	83 c0 03             	add    $0x3,%eax
    ea42:	38 d0                	cmp    %dl,%al
    ea44:	7c 08                	jl     ea4e <barriered_work+0x9e>
    ea46:	84 d2                	test   %dl,%dl
    ea48:	0f 85 6e 08 00 00    	jne    f2bc <barriered_work+0x90c>
    ea4e:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    ea55:	4c 8d 8b 08 01 00 00 	lea    0x108(%rbx),%r9
    ea5c:	75 4e                	jne    eaac <barriered_work+0xfc>
    ea5e:	48 89 fa             	mov    %rdi,%rdx
      data->n++;
    ea61:	4c 89 ce             	mov    %r9,%rsi
    while (data->scheduled == 1) {
    ea64:	48 89 f9             	mov    %rdi,%rcx
      data->n++;
    ea67:	48 c1 ee 03          	shr    $0x3,%rsi
    while (data->scheduled == 1) {
    ea6b:	83 e2 07             	and    $0x7,%edx
    ea6e:	48 c1 e9 03          	shr    $0x3,%rcx
    ea72:	83 c2 03             	add    $0x3,%edx
    ea75:	0f 1f 00             	nopl   (%rax)
      data->n++;
    ea78:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    ea7f:	0f 85 86 07 00 00    	jne    f20b <barriered_work+0x85b>
    ea85:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    ea8d:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    ea90:	0f b6 81 00 80 ff 7f 	movzbl 0x7fff8000(%rcx),%eax
    ea97:	38 c2                	cmp    %al,%dl
    ea99:	7c 08                	jl     eaa3 <barriered_work+0xf3>
    ea9b:	84 c0                	test   %al,%al
    ea9d:	0f 85 63 07 00 00    	jne    f206 <barriered_work+0x856>
    eaa3:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    eaaa:	74 cc                	je     ea78 <barriered_work+0xc8>
  if (data->sending == 1) {
    eaac:	48 8d bb 80 01 00 00 	lea    0x180(%rbx),%rdi
    eab3:	48 89 f8             	mov    %rdi,%rax
    eab6:	48 c1 e8 03          	shr    $0x3,%rax
    eaba:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    eac1:	84 c0                	test   %al,%al
    eac3:	74 08                	je     eacd <barriered_work+0x11d>
    eac5:	3c 03                	cmp    $0x3,%al
    eac7:	0f 8e ea 07 00 00    	jle    f2b7 <barriered_work+0x907>
    eacd:	83 bb 80 01 00 00 01 	cmpl   $0x1,0x180(%rbx)
    ead4:	75 08                	jne    eade <barriered_work+0x12e>
    ead6:	48 89 df             	mov    %rbx,%rdi
    ead9:	e8 92 a5 ff ff       	call   9070 <sendm.part.0>
  asm volatile ("sfence" ::: "memory");
    eade:	0f ae f8             	sfence
}
    eae1:	48 83 c4 48          	add    $0x48,%rsp
    eae5:	31 c0                	xor    %eax,%eax
    eae7:	5b                   	pop    %rbx
    eae8:	5d                   	pop    %rbp
    eae9:	41 5c                	pop    %r12
    eaeb:	41 5d                	pop    %r13
    eaed:	41 5e                	pop    %r14
    eaef:	41 5f                	pop    %r15
    eaf1:	c3                   	ret
    eaf2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      receive(data);
    eaf8:	48 89 df             	mov    %rbx,%rdi
    eafb:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    eb00:	e8 db f9 ff ff       	call   e4e0 <receive>
        int t = data->task_index;
    eb05:	4c 89 f8             	mov    %r15,%rax
    eb08:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    eb0d:	48 c1 e8 03          	shr    $0x3,%rax
    eb11:	0f b6 90 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%edx
    eb18:	4c 89 f8             	mov    %r15,%rax
    eb1b:	83 e0 07             	and    $0x7,%eax
    eb1e:	83 c0 03             	add    $0x3,%eax
    eb21:	38 d0                	cmp    %dl,%al
    eb23:	7c 08                	jl     eb2d <barriered_work+0x17d>
    eb25:	84 d2                	test   %dl,%dl
    eb27:	0f 85 3c 07 00 00    	jne    f269 <barriered_work+0x8b9>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    eb2d:	48 8d 93 40 01 00 00 	lea    0x140(%rbx),%rdx
        int t = data->task_index;
    eb34:	8b 7b 04             	mov    0x4(%rbx),%edi
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    eb37:	48 89 d0             	mov    %rdx,%rax
    eb3a:	48 c1 e8 03          	shr    $0x3,%rax
    eb3e:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    eb45:	84 c0                	test   %al,%al
    eb47:	74 08                	je     eb51 <barriered_work+0x1a1>
    eb49:	3c 03                	cmp    $0x3,%al
    eb4b:	0f 8e 20 07 00 00    	jle    f271 <barriered_work+0x8c1>
    eb51:	48 63 b3 40 01 00 00 	movslq 0x140(%rbx),%rsi
    eb58:	85 f6                	test   %esi,%esi
    eb5a:	0f 8e 8e 02 00 00    	jle    edee <barriered_work+0x43e>
              int next_task = abs((t + 1) % (data->thread_count));
    eb60:	4c 8d 83 34 01 00 00 	lea    0x134(%rbx),%r8
    eb67:	8d 47 01             	lea    0x1(%rdi),%eax
    eb6a:	4c 89 c2             	mov    %r8,%rdx
    eb6d:	48 c1 ea 03          	shr    $0x3,%rdx
    eb71:	44 0f b6 8a 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%r9d
    eb79:	4c 89 c2             	mov    %r8,%rdx
    eb7c:	83 e2 07             	and    $0x7,%edx
    eb7f:	83 c2 03             	add    $0x3,%edx
    eb82:	44 38 ca             	cmp    %r9b,%dl
    eb85:	7c 09                	jl     eb90 <barriered_work+0x1e0>
    eb87:	45 84 c9             	test   %r9b,%r9b
    eb8a:	0f 85 f6 06 00 00    	jne    f286 <barriered_work+0x8d6>
    eb90:	99                   	cltd
    eb91:	f7 bb 34 01 00 00    	idivl  0x134(%rbx)
    eb97:	89 d0                	mov    %edx,%eax
    eb99:	f7 d8                	neg    %eax
    eb9b:	0f 48 c2             	cmovs  %edx,%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    eb9e:	48 8d 93 28 01 00 00 	lea    0x128(%rbx),%rdx
    eba5:	49 89 d0             	mov    %rdx,%r8
    eba8:	49 c1 e8 03          	shr    $0x3,%r8
    ebac:	41 80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r8)
    ebb4:	0f 85 a7 06 00 00    	jne    f261 <barriered_work+0x8b1>
    ebba:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    ebc1:	4c 8d 42 20          	lea    0x20(%rdx),%r8
    ebc5:	4d 89 c1             	mov    %r8,%r9
    ebc8:	49 c1 e9 03          	shr    $0x3,%r9
    ebcc:	41 80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r9)
    ebd4:	0f 85 c1 06 00 00    	jne    f29b <barriered_work+0x8eb>
    ebda:	48 8b 52 20          	mov    0x20(%rdx),%rdx
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    ebde:	4c 63 d0             	movslq %eax,%r10
    ebe1:	48 8d 04 76          	lea    (%rsi,%rsi,2),%rax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    ebe5:	48 63 ef             	movslq %edi,%rbp
    ebe8:	48 c1 e0 06          	shl    $0x6,%rax
    ebec:	48 c1 e5 09          	shl    $0x9,%rbp
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    ebf0:	45 31 c9             	xor    %r9d,%r9d
    ebf3:	4c 8d 62 38          	lea    0x38(%rdx),%r12
    ebf7:	49 c1 e2 09          	shl    $0x9,%r10
    ebfb:	4c 8d 44 02 38       	lea    0x38(%rdx,%rax,1),%r8
    ec00:	4d 89 e3             	mov    %r12,%r11
    ec03:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    ec08:	4c 89 d8             	mov    %r11,%rax
    ec0b:	48 c1 e8 03          	shr    $0x3,%rax
    ec0f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ec16:	0f 85 96 05 00 00    	jne    f1b2 <barriered_work+0x802>
    ec1c:	49 8b 03             	mov    (%r11),%rax
    ec1f:	48 01 e8             	add    %rbp,%rax
    ec22:	48 8d b8 70 01 00 00 	lea    0x170(%rax),%rdi
    ec29:	48 89 fa             	mov    %rdi,%rdx
    ec2c:	48 c1 ea 03          	shr    $0x3,%rdx
    ec30:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    ec37:	0f 85 70 05 00 00    	jne    f1ad <barriered_work+0x7fd>
    ec3d:	48 8b b8 70 01 00 00 	mov    0x170(%rax),%rdi
    ec44:	4c 89 e0             	mov    %r12,%rax
    ec47:	48 83 c7 20          	add    $0x20,%rdi
    ec4b:	e9 dc 00 00 00       	jmp    ed2c <barriered_work+0x37c>
                 if (((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available == 0) {
    ec50:	4c 8d 6a 18          	lea    0x18(%rdx),%r13
    ec54:	4c 89 ee             	mov    %r13,%rsi
    ec57:	48 c1 ee 03          	shr    $0x3,%rsi
    ec5b:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    ec62:	40 84 f6             	test   %sil,%sil
    ec65:	74 0a                	je     ec71 <barriered_work+0x2c1>
    ec67:	40 80 fe 03          	cmp    $0x3,%sil
    ec6b:	0f 8e 1c 05 00 00    	jle    f18d <barriered_work+0x7dd>
    ec71:	8b 72 18             	mov    0x18(%rdx),%esi
    ec74:	85 f6                	test   %esi,%esi
    ec76:	0f 85 9d 00 00 00    	jne    ed19 <barriered_work+0x369>
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    ec7c:	48 89 c6             	mov    %rax,%rsi
    ec7f:	48 c1 ee 03          	shr    $0x3,%rsi
    ec83:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    ec8a:	0f 85 56 05 00 00    	jne    f1e6 <barriered_work+0x836>
    ec90:	48 8b 30             	mov    (%rax),%rsi
    ec93:	4c 01 d6             	add    %r10,%rsi
    ec96:	4c 8d ae 70 01 00 00 	lea    0x170(%rsi),%r13
    ec9d:	4d 89 ee             	mov    %r13,%r14
    eca0:	49 c1 ee 03          	shr    $0x3,%r14
    eca4:	41 80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r14)
    ecac:	0f 85 3c 05 00 00    	jne    f1ee <barriered_work+0x83e>
    ecb2:	4c 8b b6 70 01 00 00 	mov    0x170(%rsi),%r14
    ecb9:	4d 01 ce             	add    %r9,%r14
    ecbc:	4d 89 f5             	mov    %r14,%r13
    ecbf:	49 c1 ed 03          	shr    $0x3,%r13
    ecc3:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    eccb:	0f 85 25 05 00 00    	jne    f1f6 <barriered_work+0x846>
    ecd1:	49 89 16             	mov    %rdx,(%r14)
                      ((struct Data*)data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available = 1;
    ecd4:	49 8d 56 08          	lea    0x8(%r14),%rdx
    ecd8:	49 89 d5             	mov    %rdx,%r13
    ecdb:	49 c1 ed 03          	shr    $0x3,%r13
    ecdf:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    ece7:	0f 85 11 05 00 00    	jne    f1fe <barriered_work+0x84e>
    eced:	49 8b 56 08          	mov    0x8(%r14),%rdx
    ecf1:	4c 8d 6a 18          	lea    0x18(%rdx),%r13
    ecf5:	4c 89 ee             	mov    %r13,%rsi
    ecf8:	48 c1 ee 03          	shr    $0x3,%rsi
    ecfc:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    ed03:	40 84 f6             	test   %sil,%sil
    ed06:	74 0a                	je     ed12 <barriered_work+0x362>
    ed08:	40 80 fe 03          	cmp    $0x3,%sil
    ed0c:	0f 8e a8 04 00 00    	jle    f1ba <barriered_work+0x80a>
    ed12:	c7 42 18 01 00 00 00 	movl   $0x1,0x18(%rdx)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    ed19:	48 05 c0 00 00 00    	add    $0xc0,%rax
    ed1f:	48 83 c7 28          	add    $0x28,%rdi
    ed23:	4c 39 c0             	cmp    %r8,%rax
    ed26:	0f 84 ae 00 00 00    	je     edda <barriered_work+0x42a>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    ed2c:	48 89 fa             	mov    %rdi,%rdx
    ed2f:	48 c1 ea 03          	shr    $0x3,%rdx
    ed33:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    ed3a:	84 d2                	test   %dl,%dl
    ed3c:	74 09                	je     ed47 <barriered_work+0x397>
    ed3e:	80 fa 03             	cmp    $0x3,%dl
    ed41:	0f 8e 41 04 00 00    	jle    f188 <barriered_work+0x7d8>
                tmp = data->thread->all_threads[y].tasks[t].mailboxes[b].higher; 
    ed47:	48 8d 57 e8          	lea    -0x18(%rdi),%rdx
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    ed4b:	8b 37                	mov    (%rdi),%esi
                tmp = data->thread->all_threads[y].tasks[t].mailboxes[b].higher; 
    ed4d:	49 89 d5             	mov    %rdx,%r13
    ed50:	49 c1 ed 03          	shr    $0x3,%r13
    ed54:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    ed5c:	0f 85 1e 04 00 00    	jne    f180 <barriered_work+0x7d0>
    ed62:	48 8b 57 e8          	mov    -0x18(%rdi),%rdx
              if (kind == MAILBOX_FRIEND) {
    ed66:	83 fe 01             	cmp    $0x1,%esi
    ed69:	0f 85 e1 fe ff ff    	jne    ec50 <barriered_work+0x2a0>
                data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    ed6f:	48 89 c6             	mov    %rax,%rsi
    ed72:	48 c1 ee 03          	shr    $0x3,%rsi
    ed76:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    ed7d:	0f 85 22 04 00 00    	jne    f1a5 <barriered_work+0x7f5>
    ed83:	48 8b 30             	mov    (%rax),%rsi
    ed86:	4c 01 d6             	add    %r10,%rsi
    ed89:	4c 8d ae 70 01 00 00 	lea    0x170(%rsi),%r13
    ed90:	4d 89 ee             	mov    %r13,%r14
    ed93:	49 c1 ee 03          	shr    $0x3,%r14
    ed97:	41 80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r14)
    ed9f:	0f 85 f0 03 00 00    	jne    f195 <barriered_work+0x7e5>
    eda5:	4c 8b b6 70 01 00 00 	mov    0x170(%rsi),%r14
    edac:	4d 01 ce             	add    %r9,%r14
    edaf:	4d 89 f5             	mov    %r14,%r13
    edb2:	49 c1 ed 03          	shr    $0x3,%r13
    edb6:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    edbe:	0f 85 d9 03 00 00    	jne    f19d <barriered_work+0x7ed>
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    edc4:	48 05 c0 00 00 00    	add    $0xc0,%rax
                data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    edca:	49 89 16             	mov    %rdx,(%r14)
          for (int b = 0; b < data->mailbox_thread_count ; b++) {
    edcd:	48 83 c7 28          	add    $0x28,%rdi
    edd1:	4c 39 c0             	cmp    %r8,%rax
    edd4:	0f 85 52 ff ff ff    	jne    ed2c <barriered_work+0x37c>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    edda:	49 81 c3 c0 00 00 00 	add    $0xc0,%r11
    ede1:	49 83 c1 28          	add    $0x28,%r9
    ede5:	4d 39 c3             	cmp    %r8,%r11
    ede8:	0f 85 1a fe ff ff    	jne    ec08 <barriered_work+0x258>
      asm volatile ("sfence" ::: "memory");
    edee:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    edf1:	48 8d 83 50 01 00 00 	lea    0x150(%rbx),%rax
    edf8:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    edfd:	48 c1 e8 03          	shr    $0x3,%rax
    ee01:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ee08:	0f 85 1e 04 00 00    	jne    f22c <barriered_work+0x87c>
    ee0e:	48 8d 83 60 01 00 00 	lea    0x160(%rbx),%rax
    ee15:	48 8b b3 50 01 00 00 	mov    0x150(%rbx),%rsi
    ee1c:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    ee21:	48 c1 e8 03          	shr    $0x3,%rax
    ee25:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ee2c:	0f 85 04 04 00 00    	jne    f236 <barriered_work+0x886>
    ee32:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    ee39:	31 ff                	xor    %edi,%edi
    ee3b:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    int modcount = ++data->thread->protected_state->modcount;
    ee40:	4c 8d b3 28 01 00 00 	lea    0x128(%rbx),%r14
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    ee47:	48 c1 e0 05          	shl    $0x5,%rax
    ee4b:	48 01 c6             	add    %rax,%rsi
    ee4e:	e8 2d 56 ff ff       	call   4480 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    ee53:	4c 89 f0             	mov    %r14,%rax
    ee56:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    ee5b:	48 c1 e8 03          	shr    $0x3,%rax
    ee5f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ee66:	0f 85 d4 03 00 00    	jne    f240 <barriered_work+0x890>
    ee6c:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    ee73:	48 8d 78 48          	lea    0x48(%rax),%rdi
    ee77:	48 89 fe             	mov    %rdi,%rsi
    ee7a:	48 c1 ee 03          	shr    $0x3,%rsi
    ee7e:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    ee85:	0f 85 bd 03 00 00    	jne    f248 <barriered_work+0x898>
    ee8b:	48 8b 50 48          	mov    0x48(%rax),%rdx
    ee8f:	48 8d 7a 10          	lea    0x10(%rdx),%rdi
    ee93:	48 89 fe             	mov    %rdi,%rsi
    ee96:	48 c1 ee 03          	shr    $0x3,%rsi
    ee9a:	0f b6 b6 00 80 ff 7f 	movzbl 0x7fff8000(%rsi),%esi
    eea1:	40 84 f6             	test   %sil,%sil
    eea4:	74 0a                	je     eeb0 <barriered_work+0x500>
    eea6:	40 80 fe 03          	cmp    $0x3,%sil
    eeaa:	0f 8e c9 03 00 00    	jle    f279 <barriered_work+0x8c9>
    eeb0:	8b 7a 10             	mov    0x10(%rdx),%edi
    while (data->scheduled == 1) {
    eeb3:	48 8d ab 4c 01 00 00 	lea    0x14c(%rbx),%rbp
    int modcount = ++data->thread->protected_state->modcount;
    eeba:	44 8d 57 01          	lea    0x1(%rdi),%r10d
    eebe:	44 89 52 10          	mov    %r10d,0x10(%rdx)
    while (data->scheduled == 1) {
    eec2:	48 89 ea             	mov    %rbp,%rdx
    eec5:	48 c1 ea 03          	shr    $0x3,%rdx
    eec9:	44 0f b6 82 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%r8d
    eed1:	48 89 ea             	mov    %rbp,%rdx
    eed4:	83 e2 07             	and    $0x7,%edx
    eed7:	83 c2 03             	add    $0x3,%edx
    eeda:	44 38 c2             	cmp    %r8b,%dl
    eedd:	7c 09                	jl     eee8 <barriered_work+0x538>
    eedf:	45 84 c0             	test   %r8b,%r8b
    eee2:	0f 85 96 03 00 00    	jne    f27e <barriered_work+0x8ce>
    eee8:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    eeef:	4c 8d 8b 08 01 00 00 	lea    0x108(%rbx),%r9
    eef6:	0f 85 c7 01 00 00    	jne    f0c3 <barriered_work+0x713>
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    eefc:	4c 8d 9b 20 01 00 00 	lea    0x120(%rbx),%r11
    ef03:	48 89 cf             	mov    %rcx,%rdi
      data->n++;
    ef06:	4d 89 cd             	mov    %r9,%r13
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    ef09:	44 89 54 24 24       	mov    %r10d,0x24(%rsp)
    ef0e:	48 c1 ef 03          	shr    $0x3,%rdi
    ef12:	4d 89 dc             	mov    %r11,%r12
    ef15:	48 89 4c 24 28       	mov    %rcx,0x28(%rsp)
      data->n++;
    ef1a:	49 c1 ed 03          	shr    $0x3,%r13
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    ef1e:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    ef23:	49 c1 ec 03          	shr    $0x3,%r12
    ef27:	4c 89 4c 24 30       	mov    %r9,0x30(%rsp)
    ef2c:	4c 89 5c 24 38       	mov    %r11,0x38(%rsp)
    ef31:	eb 20                	jmp    ef53 <barriered_work+0x5a3>
    ef33:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (modcount != data->thread->protected_state->modcount) {
    ef38:	4c 89 f0             	mov    %r14,%rax
    ef3b:	48 c1 e8 03          	shr    $0x3,%rax
    ef3f:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ef46:	0f 85 85 03 00 00    	jne    f2d1 <barriered_work+0x921>
    ef4c:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
      data->n++;
    ef53:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    ef5b:	0f 85 71 02 00 00    	jne    f1d2 <barriered_work+0x822>
    ef61:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    ef69:	41 80 bc 24 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r12)
    ef72:	0f 85 64 02 00 00    	jne    f1dc <barriered_work+0x82c>
    ef78:	48 8d 78 18          	lea    0x18(%rax),%rdi
    ef7c:	48 8b 8b 20 01 00 00 	mov    0x120(%rbx),%rcx
    ef83:	48 89 fe             	mov    %rdi,%rsi
    ef86:	48 c1 ee 03          	shr    $0x3,%rsi
    ef8a:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    ef91:	0f 85 7c 02 00 00    	jne    f213 <barriered_work+0x863>
    ef97:	48 8b 70 18          	mov    0x18(%rax),%rsi
    ef9b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    efa0:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    efa7:	84 c0                	test   %al,%al
    efa9:	74 08                	je     efb3 <barriered_work+0x603>
    efab:	3c 03                	cmp    $0x3,%al
    efad:	0f 8e 65 02 00 00    	jle    f218 <barriered_work+0x868>
    efb3:	48 63 83 30 01 00 00 	movslq 0x130(%rbx),%rax
    efba:	48 8d 3c c6          	lea    (%rsi,%rax,8),%rdi
    efbe:	48 89 f8             	mov    %rdi,%rax
    efc1:	48 c1 e8 03          	shr    $0x3,%rax
    efc5:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    efcc:	0f 85 50 02 00 00    	jne    f222 <barriered_work+0x872>
    efd2:	48 8b 07             	mov    (%rdi),%rax
    efd5:	48 8d 78 38          	lea    0x38(%rax),%rdi
    efd9:	48 89 fe             	mov    %rdi,%rsi
    efdc:	48 c1 ee 03          	shr    $0x3,%rsi
    efe0:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    efe7:	0f 85 3a 02 00 00    	jne    f227 <barriered_work+0x877>
    efed:	48 8b 78 38          	mov    0x38(%rax),%rdi
    eff1:	4c 89 f8             	mov    %r15,%rax
    eff4:	48 c1 e8 03          	shr    $0x3,%rax
    eff8:	0f b6 b0 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%esi
    efff:	4c 89 f8             	mov    %r15,%rax
    f002:	83 e0 07             	and    $0x7,%eax
    f005:	83 c0 03             	add    $0x3,%eax
    f008:	40 38 f0             	cmp    %sil,%al
    f00b:	7c 09                	jl     f016 <barriered_work+0x666>
    f00d:	40 84 f6             	test   %sil,%sil
    f010:	0f 85 ac 01 00 00    	jne    f1c2 <barriered_work+0x812>
    f016:	48 63 43 04          	movslq 0x4(%rbx),%rax
    f01a:	48 c1 e0 09          	shl    $0x9,%rax
    f01e:	48 01 c7             	add    %rax,%rdi
    f021:	ff d1                	call   *%rcx
      asm volatile ("sfence" ::: "memory");
    f023:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    f026:	48 89 e8             	mov    %rbp,%rax
    f029:	48 c1 e8 03          	shr    $0x3,%rax
    f02d:	0f b6 88 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%ecx
    f034:	48 89 e8             	mov    %rbp,%rax
    f037:	83 e0 07             	and    $0x7,%eax
    f03a:	83 c0 03             	add    $0x3,%eax
    f03d:	38 c8                	cmp    %cl,%al
    f03f:	7c 08                	jl     f049 <barriered_work+0x699>
    f041:	84 c9                	test   %cl,%cl
    f043:	0f 85 81 01 00 00    	jne    f1ca <barriered_work+0x81a>
    f049:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    f050:	0f 84 e2 fe ff ff    	je     ef38 <barriered_work+0x588>
    if (modcount != data->thread->protected_state->modcount) {
    f056:	4c 89 f0             	mov    %r14,%rax
    f059:	44 8b 54 24 24       	mov    0x24(%rsp),%r10d
    f05e:	48 c1 e8 03          	shr    $0x3,%rax
    f062:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    f069:	0f 85 24 02 00 00    	jne    f293 <barriered_work+0x8e3>
    f06f:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    f076:	48 8d 78 48          	lea    0x48(%rax),%rdi
    f07a:	48 89 fa             	mov    %rdi,%rdx
    f07d:	48 c1 ea 03          	shr    $0x3,%rdx
    f081:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f088:	0f 85 15 02 00 00    	jne    f2a3 <barriered_work+0x8f3>
    f08e:	48 8b 40 48          	mov    0x48(%rax),%rax
    f092:	48 8d 78 10          	lea    0x10(%rax),%rdi
    f096:	48 89 fa             	mov    %rdi,%rdx
    f099:	48 c1 ea 03          	shr    $0x3,%rdx
    f09d:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    f0a4:	84 d2                	test   %dl,%dl
    f0a6:	74 09                	je     f0b1 <barriered_work+0x701>
    f0a8:	80 fa 03             	cmp    $0x3,%dl
    f0ab:	0f 8e dd 01 00 00    	jle    f28e <barriered_work+0x8de>
    f0b1:	44 3b 50 10          	cmp    0x10(%rax),%r10d
    f0b5:	74 0c                	je     f0c3 <barriered_work+0x713>
    f0b7:	48 8d 3d a2 2d 00 00 	lea    0x2da2(%rip),%rdi        # 11e60 <_IO_stdin_used+0xe60>
    f0be:	e8 3d 57 ff ff       	call   4800 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    f0c3:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    f0c8:	48 c1 e8 03          	shr    $0x3,%rax
    f0cc:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    f0d3:	0f 85 cf 01 00 00    	jne    f2a8 <barriered_work+0x8f8>
    f0d9:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    f0de:	48 8b 93 50 01 00 00 	mov    0x150(%rbx),%rdx
    f0e5:	48 c1 ed 03          	shr    $0x3,%rbp
    f0e9:	80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rbp)
    f0f0:	0f 85 57 01 00 00    	jne    f24d <barriered_work+0x89d>
    f0f6:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    f0fd:	31 ff                	xor    %edi,%edi
    f0ff:	48 c1 e0 05          	shl    $0x5,%rax
    f103:	48 8d 74 02 10       	lea    0x10(%rdx,%rax,1),%rsi
    f108:	e8 73 53 ff ff       	call   4480 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    f10d:	80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rbp)
    f114:	0f 85 3d 01 00 00    	jne    f257 <barriered_work+0x8a7>
    f11a:	48 8d bb 58 01 00 00 	lea    0x158(%rbx),%rdi
    f121:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    f128:	48 89 fa             	mov    %rdi,%rdx
    f12b:	48 c1 ea 03          	shr    $0x3,%rdx
    f12f:	48 83 c0 01          	add    $0x1,%rax
    f133:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f13a:	0f 85 72 01 00 00    	jne    f2b2 <barriered_work+0x902>
    f140:	48 99                	cqto
  if (data->sending == 1) {
    f142:	48 8d bb 80 01 00 00 	lea    0x180(%rbx),%rdi
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    f149:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
  if (data->sending == 1) {
    f150:	48 89 f8             	mov    %rdi,%rax
    f153:	48 c1 e8 03          	shr    $0x3,%rax
    f157:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    f15e:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
  if (data->sending == 1) {
    f165:	84 c0                	test   %al,%al
    f167:	0f 84 60 f9 ff ff    	je     eacd <barriered_work+0x11d>
    f16d:	3c 03                	cmp    $0x3,%al
    f16f:	0f 8f 58 f9 ff ff    	jg     eacd <barriered_work+0x11d>
    f175:	e8 d6 53 ff ff       	call   4550 <__asan_report_load4@plt>
    f17a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
                tmp = data->thread->all_threads[y].tasks[t].mailboxes[b].higher; 
    f180:	48 89 d7             	mov    %rdx,%rdi
    f183:	e8 58 53 ff ff       	call   44e0 <__asan_report_load8@plt>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    f188:	e8 c3 53 ff ff       	call   4550 <__asan_report_load4@plt>
                 if (((struct Data*) data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available == 0) {
    f18d:	4c 89 ef             	mov    %r13,%rdi
    f190:	e8 bb 53 ff ff       	call   4550 <__asan_report_load4@plt>
                data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    f195:	4c 89 ef             	mov    %r13,%rdi
    f198:	e8 43 53 ff ff       	call   44e0 <__asan_report_load8@plt>
    f19d:	4c 89 f7             	mov    %r14,%rdi
    f1a0:	e8 2b 55 ff ff       	call   46d0 <__asan_report_store8@plt>
    f1a5:	48 89 c7             	mov    %rax,%rdi
    f1a8:	e8 33 53 ff ff       	call   44e0 <__asan_report_load8@plt>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    f1ad:	e8 2e 53 ff ff       	call   44e0 <__asan_report_load8@plt>
    f1b2:	4c 89 df             	mov    %r11,%rdi
    f1b5:	e8 26 53 ff ff       	call   44e0 <__asan_report_load8@plt>
                      ((struct Data*)data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available = 1;
    f1ba:	4c 89 ef             	mov    %r13,%rdi
    f1bd:	e8 fe 54 ff ff       	call   46c0 <__asan_report_store4@plt>
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    f1c2:	4c 89 ff             	mov    %r15,%rdi
    f1c5:	e8 86 53 ff ff       	call   4550 <__asan_report_load4@plt>
    while (data->scheduled == 1) {
    f1ca:	48 89 ef             	mov    %rbp,%rdi
    f1cd:	e8 7e 53 ff ff       	call   4550 <__asan_report_load4@plt>
      data->n++;
    f1d2:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    f1d7:	e8 04 53 ff ff       	call   44e0 <__asan_report_load8@plt>
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    f1dc:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    f1e1:	e8 fa 52 ff ff       	call   44e0 <__asan_report_load8@plt>
                  data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = tmp;
    f1e6:	48 89 c7             	mov    %rax,%rdi
    f1e9:	e8 f2 52 ff ff       	call   44e0 <__asan_report_load8@plt>
    f1ee:	4c 89 ef             	mov    %r13,%rdi
    f1f1:	e8 ea 52 ff ff       	call   44e0 <__asan_report_load8@plt>
    f1f6:	4c 89 f7             	mov    %r14,%rdi
    f1f9:	e8 d2 54 ff ff       	call   46d0 <__asan_report_store8@plt>
                      ((struct Data*)data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available = 1;
    f1fe:	48 89 d7             	mov    %rdx,%rdi
    f201:	e8 da 52 ff ff       	call   44e0 <__asan_report_load8@plt>
    while (data->scheduled == 1) {
    f206:	e8 45 53 ff ff       	call   4550 <__asan_report_load4@plt>
      data->n++;
    f20b:	4c 89 cf             	mov    %r9,%rdi
    f20e:	e8 cd 52 ff ff       	call   44e0 <__asan_report_load8@plt>
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    f213:	e8 c8 52 ff ff       	call   44e0 <__asan_report_load8@plt>
    f218:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    f21d:	e8 2e 53 ff ff       	call   4550 <__asan_report_load4@plt>
    f222:	e8 b9 52 ff ff       	call   44e0 <__asan_report_load8@plt>
    f227:	e8 b4 52 ff ff       	call   44e0 <__asan_report_load8@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    f22c:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    f231:	e8 aa 52 ff ff       	call   44e0 <__asan_report_load8@plt>
    f236:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    f23b:	e8 a0 52 ff ff       	call   44e0 <__asan_report_load8@plt>
    int modcount = ++data->thread->protected_state->modcount;
    f240:	4c 89 f7             	mov    %r14,%rdi
    f243:	e8 98 52 ff ff       	call   44e0 <__asan_report_load8@plt>
    f248:	e8 93 52 ff ff       	call   44e0 <__asan_report_load8@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    f24d:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    f252:	e8 89 52 ff ff       	call   44e0 <__asan_report_load8@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    f257:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    f25c:	e8 7f 52 ff ff       	call   44e0 <__asan_report_load8@plt>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    f261:	48 89 d7             	mov    %rdx,%rdi
    f264:	e8 77 52 ff ff       	call   44e0 <__asan_report_load8@plt>
        int t = data->task_index;
    f269:	4c 89 ff             	mov    %r15,%rdi
    f26c:	e8 df 52 ff ff       	call   4550 <__asan_report_load4@plt>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    f271:	48 89 d7             	mov    %rdx,%rdi
    f274:	e8 d7 52 ff ff       	call   4550 <__asan_report_load4@plt>
    int modcount = ++data->thread->protected_state->modcount;
    f279:	e8 d2 52 ff ff       	call   4550 <__asan_report_load4@plt>
    while (data->scheduled == 1) {
    f27e:	48 89 ef             	mov    %rbp,%rdi
    f281:	e8 ca 52 ff ff       	call   4550 <__asan_report_load4@plt>
              int next_task = abs((t + 1) % (data->thread_count));
    f286:	4c 89 c7             	mov    %r8,%rdi
    f289:	e8 c2 52 ff ff       	call   4550 <__asan_report_load4@plt>
    if (modcount != data->thread->protected_state->modcount) {
    f28e:	e8 bd 52 ff ff       	call   4550 <__asan_report_load4@plt>
    f293:	4c 89 f7             	mov    %r14,%rdi
    f296:	e8 45 52 ff ff       	call   44e0 <__asan_report_load8@plt>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    f29b:	4c 89 c7             	mov    %r8,%rdi
    f29e:	e8 3d 52 ff ff       	call   44e0 <__asan_report_load8@plt>
    if (modcount != data->thread->protected_state->modcount) {
    f2a3:	e8 38 52 ff ff       	call   44e0 <__asan_report_load8@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    f2a8:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    f2ad:	e8 2e 52 ff ff       	call   44e0 <__asan_report_load8@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    f2b2:	e8 29 52 ff ff       	call   44e0 <__asan_report_load8@plt>
  if (data->sending == 1) {
    f2b7:	e8 94 52 ff ff       	call   4550 <__asan_report_load4@plt>
    while (data->scheduled == 1) {
    f2bc:	e8 8f 52 ff ff       	call   4550 <__asan_report_load4@plt>
  if (data->thread_index == data->task_index) {
    f2c1:	4c 89 ff             	mov    %r15,%rdi
    f2c4:	e8 87 52 ff ff       	call   4550 <__asan_report_load4@plt>
    f2c9:	48 89 cf             	mov    %rcx,%rdi
    f2cc:	e8 7f 52 ff ff       	call   4550 <__asan_report_load4@plt>
    if (modcount != data->thread->protected_state->modcount) {
    f2d1:	4c 89 f7             	mov    %r14,%rdi
    f2d4:	e8 07 52 ff ff       	call   44e0 <__asan_report_load8@plt>
    f2d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

000000000000f2e0 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    f2e0:	f3 0f 1e fa          	endbr64
    f2e4:	53                   	push   %rbx
    f2e5:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    f2e8:	e8 93 e3 ff ff       	call   d680 <barriered_work_ingest>
  barriered_work(data);
    f2ed:	48 89 df             	mov    %rbx,%rdi
}
    f2f0:	5b                   	pop    %rbx
  barriered_work(data);
    f2f1:	e9 ba f6 ff ff       	jmp    e9b0 <barriered_work>
    f2f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

000000000000f300 <sendm>:
int sendm(struct BarrierTask *data) {
    f300:	f3 0f 1e fa          	endbr64
  if (data->sending == 1) {
    f304:	48 8d 97 80 01 00 00 	lea    0x180(%rdi),%rdx
int sendm(struct BarrierTask *data) {
    f30b:	48 83 ec 08          	sub    $0x8,%rsp
  if (data->sending == 1) {
    f30f:	48 89 d0             	mov    %rdx,%rax
    f312:	48 c1 e8 03          	shr    $0x3,%rax
    f316:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    f31d:	84 c0                	test   %al,%al
    f31f:	74 04                	je     f325 <sendm+0x25>
    f321:	3c 03                	cmp    $0x3,%al
    f323:	7e 15                	jle    f33a <sendm+0x3a>
    f325:	83 bf 80 01 00 00 01 	cmpl   $0x1,0x180(%rdi)
    f32c:	75 05                	jne    f333 <sendm+0x33>
    f32e:	e8 3d 9d ff ff       	call   9070 <sendm.part.0>
}
    f333:	31 c0                	xor    %eax,%eax
    f335:	48 83 c4 08          	add    $0x8,%rsp
    f339:	c3                   	ret
  if (data->sending == 1) {
    f33a:	48 89 d7             	mov    %rdx,%rdi
    f33d:	e8 0e 52 ff ff       	call   4550 <__asan_report_load4@plt>
    f342:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    f34d:	0f 1f 00             	nopl   (%rax)

000000000000f350 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    f350:	f3 0f 1e fa          	endbr64
}
    f354:	31 c0                	xor    %eax,%eax
    f356:	c3                   	ret
    f357:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

000000000000f360 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    f360:	f3 0f 1e fa          	endbr64
    f364:	31 c0                	xor    %eax,%eax
    f366:	c3                   	ret
    f367:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

000000000000f370 <after>:
int after(struct timespec left, struct timespec right) {
    f370:	f3 0f 1e fa          	endbr64
    f374:	41 57                	push   %r15
    f376:	49 89 cf             	mov    %rcx,%r15
    f379:	41 56                	push   %r14
    f37b:	49 89 d6             	mov    %rdx,%r14
    f37e:	41 55                	push   %r13
    f380:	55                   	push   %rbp
    f381:	48 89 fd             	mov    %rdi,%rbp
    f384:	53                   	push   %rbx
    f385:	48 81 ec 90 00 00 00 	sub    $0x90,%rsp
    f38c:	8b 05 6e 77 00 00    	mov    0x776e(%rip),%eax        # 16b00 <__asan_option_detect_stack_use_after_return@@Base>
    f392:	48 8d 5c 24 10       	lea    0x10(%rsp),%rbx
    f397:	49 89 dd             	mov    %rbx,%r13
    f39a:	85 c0                	test   %eax,%eax
    f39c:	0f 85 2e 01 00 00    	jne    f4d0 <after+0x160>
    f3a2:	48 8d 05 27 3c 00 00 	lea    0x3c27(%rip),%rax        # 12fd0 <_IO_stdin_used+0x1fd0>
    f3a9:	48 c7 03 b3 8a b5 41 	movq   $0x41b58ab3,(%rbx)
  return left.tv_sec > right.tv_sec &&
    f3b0:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
int after(struct timespec left, struct timespec right) {
    f3b4:	48 89 43 08          	mov    %rax,0x8(%rbx)
    f3b8:	48 8d 05 b1 ff ff ff 	lea    -0x4f(%rip),%rax        # f370 <after>
    f3bf:	48 8d 8b 80 00 00 00 	lea    0x80(%rbx),%rcx
    f3c6:	48 89 43 10          	mov    %rax,0x10(%rbx)
    f3ca:	48 89 d8             	mov    %rbx,%rax
    f3cd:	48 c1 e8 03          	shr    $0x3,%rax
    f3d1:	c7 80 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%rax)
    f3db:	c7 80 04 80 ff 7f 00 00 f2 f2 	movl   $0xf2f20000,0x7fff8004(%rax)
    f3e5:	c7 80 08 80 ff 7f 00 00 f3 f3 	movl   $0xf3f30000,0x7fff8008(%rax)
    f3ef:	64 48 8b 14 25 28 00 00 00 	mov    %fs:0x28,%rdx
    f3f8:	48 89 94 24 88 00 00 00 	mov    %rdx,0x88(%rsp)
    f400:	31 d2                	xor    %edx,%edx
  return left.tv_sec > right.tv_sec &&
    f402:	48 89 fa             	mov    %rdi,%rdx
int after(struct timespec left, struct timespec right) {
    f405:	48 89 69 a0          	mov    %rbp,-0x60(%rcx)
  return left.tv_sec > right.tv_sec &&
    f409:	48 c1 ea 03          	shr    $0x3,%rdx
int after(struct timespec left, struct timespec right) {
    f40d:	48 89 71 a8          	mov    %rsi,-0x58(%rcx)
  return left.tv_sec > right.tv_sec &&
    f411:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
int after(struct timespec left, struct timespec right) {
    f418:	4c 89 71 c0          	mov    %r14,-0x40(%rcx)
    f41c:	4c 89 79 c8          	mov    %r15,-0x38(%rcx)
  return left.tv_sec > right.tv_sec &&
    f420:	0f 85 a5 00 00 00    	jne    f4cb <after+0x15b>
    f426:	48 8d 7b 40          	lea    0x40(%rbx),%rdi
    f42a:	48 89 fa             	mov    %rdi,%rdx
    f42d:	48 c1 ea 03          	shr    $0x3,%rdx
    f431:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f438:	0f 85 88 00 00 00    	jne    f4c6 <after+0x156>
    f43e:	48 3b 69 c0          	cmp    -0x40(%rcx),%rbp
    f442:	7e 74                	jle    f4b8 <after+0x148>
         left.tv_nsec > right.tv_nsec;
    f444:	48 8d 7b 28          	lea    0x28(%rbx),%rdi
    f448:	48 89 fa             	mov    %rdi,%rdx
    f44b:	48 c1 ea 03          	shr    $0x3,%rdx
    f44f:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f456:	75 69                	jne    f4c1 <after+0x151>
    f458:	48 8d 7b 48          	lea    0x48(%rbx),%rdi
    f45c:	48 89 fa             	mov    %rdi,%rdx
    f45f:	48 c1 ea 03          	shr    $0x3,%rdx
    f463:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f46a:	75 50                	jne    f4bc <after+0x14c>
  return left.tv_sec > right.tv_sec &&
    f46c:	31 d2                	xor    %edx,%edx
    f46e:	48 3b 71 c8          	cmp    -0x38(%rcx),%rsi
    f472:	0f 9f c2             	setg   %dl
int after(struct timespec left, struct timespec right) {
    f475:	49 39 dd             	cmp    %rbx,%r13
    f478:	75 76                	jne    f4f0 <after+0x180>
    f47a:	48 c7 80 00 80 ff 7f 00 00 00 00 	movq   $0x0,0x7fff8000(%rax)
    f485:	c7 80 08 80 ff 7f 00 00 00 00 	movl   $0x0,0x7fff8008(%rax)
}
    f48f:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
    f497:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    f4a0:	75 7c                	jne    f51e <after+0x1ae>
    f4a2:	48 81 c4 90 00 00 00 	add    $0x90,%rsp
    f4a9:	89 d0                	mov    %edx,%eax
    f4ab:	5b                   	pop    %rbx
    f4ac:	5d                   	pop    %rbp
    f4ad:	41 5d                	pop    %r13
    f4af:	41 5e                	pop    %r14
    f4b1:	41 5f                	pop    %r15
    f4b3:	c3                   	ret
    f4b4:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    f4b8:	31 d2                	xor    %edx,%edx
    f4ba:	eb b9                	jmp    f475 <after+0x105>
         left.tv_nsec > right.tv_nsec;
    f4bc:	e8 1f 50 ff ff       	call   44e0 <__asan_report_load8@plt>
    f4c1:	e8 1a 50 ff ff       	call   44e0 <__asan_report_load8@plt>
  return left.tv_sec > right.tv_sec &&
    f4c6:	e8 15 50 ff ff       	call   44e0 <__asan_report_load8@plt>
    f4cb:	e8 10 50 ff ff       	call   44e0 <__asan_report_load8@plt>
int after(struct timespec left, struct timespec right) {
    f4d0:	bf 60 00 00 00       	mov    $0x60,%edi
    f4d5:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    f4da:	e8 11 50 ff ff       	call   44f0 <__asan_stack_malloc_1@plt>
    f4df:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    f4e4:	48 85 c0             	test   %rax,%rax
    f4e7:	48 0f 45 d8          	cmovne %rax,%rbx
    f4eb:	e9 b2 fe ff ff       	jmp    f3a2 <after+0x32>
    f4f0:	48 b9 f5 f5 f5 f5 f5 f5 f5 f5 	movabs $0xf5f5f5f5f5f5f5f5,%rcx
    f4fa:	48 c7 03 0e 36 e0 45 	movq   $0x45e0360e,(%rbx)
    f501:	48 89 88 00 80 ff 7f 	mov    %rcx,0x7fff8000(%rax)
    f508:	c7 80 08 80 ff 7f f5 f5 f5 f5 	movl   $0xf5f5f5f5,0x7fff8008(%rax)
    f512:	48 8b 43 78          	mov    0x78(%rbx),%rax
    f516:	c6 00 00             	movb   $0x0,(%rax)
    f519:	e9 71 ff ff ff       	jmp    f48f <after+0x11f>
}
    f51e:	e8 8d 51 ff ff       	call   46b0 <__stack_chk_fail@plt>
    f523:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    f52e:	66 90                	xchg   %ax,%ax

000000000000f530 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    f530:	f3 0f 1e fa          	endbr64
    f534:	41 57                	push   %r15
    f536:	41 56                	push   %r14
    f538:	49 89 f6             	mov    %rsi,%r14
    f53b:	41 55                	push   %r13
    f53d:	49 89 cd             	mov    %rcx,%r13
    f540:	41 54                	push   %r12
    f542:	49 89 d4             	mov    %rdx,%r12
    f545:	55                   	push   %rbp
    f546:	48 89 fd             	mov    %rdi,%rbp
    f549:	53                   	push   %rbx
    f54a:	48 81 ec d8 00 00 00 	sub    $0xd8,%rsp
    f551:	8b 05 a9 75 00 00    	mov    0x75a9(%rip),%eax        # 16b00 <__asan_option_detect_stack_use_after_return@@Base>
    f557:	48 8d 5c 24 10       	lea    0x10(%rsp),%rbx
    f55c:	49 89 df             	mov    %rbx,%r15
    f55f:	85 c0                	test   %eax,%eax
    f561:	0f 85 05 02 00 00    	jne    f76c <within+0x23c>
    f567:	48 8d 35 8a 3a 00 00 	lea    0x3a8a(%rip),%rsi        # 12ff8 <_IO_stdin_used+0x1ff8>
    f56e:	48 89 d9             	mov    %rbx,%rcx
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f571:	48 8d 7b 20          	lea    0x20(%rbx),%rdi
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    f575:	48 c7 03 b3 8a b5 41 	movq   $0x41b58ab3,(%rbx)
    f57c:	48 89 73 08          	mov    %rsi,0x8(%rbx)
    f580:	48 c1 e9 03          	shr    $0x3,%rcx
    f584:	48 8d 35 a5 ff ff ff 	lea    -0x5b(%rip),%rsi        # f530 <within>
    f58b:	48 8d 83 c0 00 00 00 	lea    0xc0(%rbx),%rax
    f592:	48 89 73 10          	mov    %rsi,0x10(%rbx)
    f596:	f3 0f 6f 8c 24 10 01 00 00 	movdqu 0x110(%rsp),%xmm1
    f59f:	c7 81 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%rcx)
    f5a9:	c7 81 04 80 ff 7f 00 00 f2 f2 	movl   $0xf2f20000,0x7fff8004(%rcx)
    f5b3:	c7 81 08 80 ff 7f 00 00 f2 f2 	movl   $0xf2f20000,0x7fff8008(%rcx)
    f5bd:	c7 81 0c 80 ff 7f 00 00 f2 f2 	movl   $0xf2f20000,0x7fff800c(%rcx)
    f5c7:	c7 81 10 80 ff 7f 00 00 f3 f3 	movl   $0xf3f30000,0x7fff8010(%rcx)
    f5d1:	64 48 8b 14 25 28 00 00 00 	mov    %fs:0x28,%rdx
    f5da:	48 89 94 24 c8 00 00 00 	mov    %rdx,0xc8(%rsp)
    f5e2:	31 d2                	xor    %edx,%edx
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f5e4:	48 89 fa             	mov    %rdi,%rdx
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    f5e7:	48 89 a8 60 ff ff ff 	mov    %rbp,-0xa0(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f5ee:	48 c1 ea 03          	shr    $0x3,%rdx
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    f5f2:	4c 89 b0 68 ff ff ff 	mov    %r14,-0x98(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f5f9:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    f600:	4c 89 60 80          	mov    %r12,-0x80(%rax)
    f604:	4c 89 68 88          	mov    %r13,-0x78(%rax)
    f608:	4c 89 40 a0          	mov    %r8,-0x60(%rax)
    f60c:	4c 89 48 a8          	mov    %r9,-0x58(%rax)
    f610:	0f 11 48 c0          	movups %xmm1,-0x40(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f614:	0f 85 4d 01 00 00    	jne    f767 <within+0x237>
    f61a:	48 8d 7b 40          	lea    0x40(%rbx),%rdi
    f61e:	48 89 fa             	mov    %rdi,%rdx
    f621:	48 c1 ea 03          	shr    $0x3,%rdx
    f625:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f62c:	0f 85 30 01 00 00    	jne    f762 <within+0x232>
    f632:	48 3b 68 80          	cmp    -0x80(%rax),%rbp
    f636:	0f 8f 04 01 00 00    	jg     f740 <within+0x210>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    f63c:	48 8d 7b 60          	lea    0x60(%rbx),%rdi
    f640:	48 89 fa             	mov    %rdi,%rdx
    f643:	48 c1 ea 03          	shr    $0x3,%rdx
    f647:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f64e:	0f 85 09 01 00 00    	jne    f75d <within+0x22d>
    f654:	48 8d 7b 68          	lea    0x68(%rbx),%rdi
    f658:	4c 8b 50 a0          	mov    -0x60(%rax),%r10
    f65c:	48 89 fa             	mov    %rdi,%rdx
    f65f:	48 c1 ea 03          	shr    $0x3,%rdx
    f663:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f66a:	0f 85 e8 00 00 00    	jne    f758 <within+0x228>
    f670:	48 8d bb 80 00 00 00 	lea    0x80(%rbx),%rdi
    f677:	4c 8b 40 a8          	mov    -0x58(%rax),%r8
    f67b:	48 89 fa             	mov    %rdi,%rdx
    f67e:	48 c1 ea 03          	shr    $0x3,%rdx
    f682:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f689:	0f 85 c4 00 00 00    	jne    f753 <within+0x223>
    f68f:	48 8d bb 88 00 00 00 	lea    0x88(%rbx),%rdi
    f696:	4c 8b 48 c0          	mov    -0x40(%rax),%r9
    f69a:	48 89 fa             	mov    %rdi,%rdx
    f69d:	48 c1 ea 03          	shr    $0x3,%rdx
    f6a1:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f6a8:	0f 85 a0 00 00 00    	jne    f74e <within+0x21e>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f6ae:	48 8d 7b 28          	lea    0x28(%rbx),%rdi
    f6b2:	48 8b 70 c8          	mov    -0x38(%rax),%rsi
    f6b6:	48 89 fa             	mov    %rdi,%rdx
    f6b9:	48 c1 ea 03          	shr    $0x3,%rdx
    f6bd:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f6c4:	0f 85 7f 00 00 00    	jne    f749 <within+0x219>
    f6ca:	48 8d 7b 48          	lea    0x48(%rbx),%rdi
    f6ce:	48 89 fa             	mov    %rdi,%rdx
    f6d1:	48 c1 ea 03          	shr    $0x3,%rdx
    f6d5:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    f6dc:	75 66                	jne    f744 <within+0x214>
    f6de:	4c 3b 70 88          	cmp    -0x78(%rax),%r14
    f6e2:	0f 9e c2             	setle  %dl
    f6e5:	4d 39 ca             	cmp    %r9,%r10
    f6e8:	0f 9e c0             	setle  %al
    f6eb:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    f6ed:	31 c0                	xor    %eax,%eax
    f6ef:	49 39 f0             	cmp    %rsi,%r8
    f6f2:	0f 9e c0             	setle  %al
    f6f5:	21 d0                	and    %edx,%eax
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    f6f7:	49 39 df             	cmp    %rbx,%r15
    f6fa:	0f 85 94 00 00 00    	jne    f794 <within+0x264>
    f700:	c7 81 10 80 ff 7f 00 00 00 00 	movl   $0x0,0x7fff8010(%rcx)
    f70a:	66 0f ef c0          	pxor   %xmm0,%xmm0
    f70e:	0f 11 81 00 80 ff 7f 	movups %xmm0,0x7fff8000(%rcx)
}
    f715:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    f71d:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
    f726:	0f 85 97 00 00 00    	jne    f7c3 <within+0x293>
    f72c:	48 81 c4 d8 00 00 00 	add    $0xd8,%rsp
    f733:	5b                   	pop    %rbx
    f734:	5d                   	pop    %rbp
    f735:	41 5c                	pop    %r12
    f737:	41 5d                	pop    %r13
    f739:	41 5e                	pop    %r14
    f73b:	41 5f                	pop    %r15
    f73d:	c3                   	ret
    f73e:	66 90                	xchg   %ax,%ax
  return 0;
    f740:	31 c0                	xor    %eax,%eax
    f742:	eb b3                	jmp    f6f7 <within+0x1c7>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f744:	e8 97 4d ff ff       	call   44e0 <__asan_report_load8@plt>
    f749:	e8 92 4d ff ff       	call   44e0 <__asan_report_load8@plt>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    f74e:	e8 8d 4d ff ff       	call   44e0 <__asan_report_load8@plt>
    f753:	e8 88 4d ff ff       	call   44e0 <__asan_report_load8@plt>
    f758:	e8 83 4d ff ff       	call   44e0 <__asan_report_load8@plt>
    f75d:	e8 7e 4d ff ff       	call   44e0 <__asan_report_load8@plt>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f762:	e8 79 4d ff ff       	call   44e0 <__asan_report_load8@plt>
    f767:	e8 74 4d ff ff       	call   44e0 <__asan_report_load8@plt>
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    f76c:	bf a0 00 00 00       	mov    $0xa0,%edi
    f771:	4c 89 04 24          	mov    %r8,(%rsp)
    f775:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    f77a:	e8 51 4d ff ff       	call   44d0 <__asan_stack_malloc_2@plt>
    f77f:	4c 8b 04 24          	mov    (%rsp),%r8
    f783:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    f788:	48 85 c0             	test   %rax,%rax
    f78b:	48 0f 45 d8          	cmovne %rax,%rbx
    f78f:	e9 d3 fd ff ff       	jmp    f567 <within+0x37>
    f794:	66 0f 6f 05 34 3c 00 00 	movdqa 0x3c34(%rip),%xmm0        # 133d0 <_IO_stdin_used+0x23d0>
    f79c:	48 c7 03 0e 36 e0 45 	movq   $0x45e0360e,(%rbx)
    f7a3:	c7 81 10 80 ff 7f f5 f5 f5 f5 	movl   $0xf5f5f5f5,0x7fff8010(%rcx)
    f7ad:	0f 11 81 00 80 ff 7f 	movups %xmm0,0x7fff8000(%rcx)
    f7b4:	48 8b 93 f8 00 00 00 	mov    0xf8(%rbx),%rdx
    f7bb:	c6 02 00             	movb   $0x0,(%rdx)
    f7be:	e9 52 ff ff ff       	jmp    f715 <within+0x1e5>
}
    f7c3:	e8 e8 4e ff ff       	call   46b0 <__stack_chk_fail@plt>
    f7c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

000000000000f7d0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    f7d0:	f3 0f 1e fa          	endbr64
    f7d4:	41 55                	push   %r13
    f7d6:	41 54                	push   %r12
    f7d8:	55                   	push   %rbp
    f7d9:	53                   	push   %rbx
    f7da:	48 81 ec c8 00 00 00 	sub    $0xc8,%rsp
    f7e1:	8b 05 19 73 00 00    	mov    0x7319(%rip),%eax        # 16b00 <__asan_option_detect_stack_use_after_return@@Base>
    f7e7:	48 89 e3             	mov    %rsp,%rbx
    f7ea:	48 89 dd             	mov    %rbx,%rbp
    f7ed:	85 c0                	test   %eax,%eax
    f7ef:	0f 85 e1 02 00 00    	jne    fad6 <overlap+0x306>
    f7f5:	48 8d 3d 3c 38 00 00 	lea    0x383c(%rip),%rdi        # 13038 <_IO_stdin_used+0x2038>
    f7fc:	48 89 da             	mov    %rbx,%rdx
    f7ff:	48 c7 03 b3 8a b5 41 	movq   $0x41b58ab3,(%rbx)
    f806:	48 8d 83 c0 00 00 00 	lea    0xc0(%rbx),%rax
    f80d:	48 89 7b 08          	mov    %rdi,0x8(%rbx)
    f811:	48 c1 ea 03          	shr    $0x3,%rdx
    f815:	48 8d 3d b4 ff ff ff 	lea    -0x4c(%rip),%rdi        # f7d0 <overlap>
    f81c:	48 89 7b 10          	mov    %rdi,0x10(%rbx)
  return left.tv_sec > right.tv_sec &&
    f820:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
int overlap(struct Snapshot left, struct Snapshot right) {
    f824:	f3 0f 6f 8c 24 f0 00 00 00 	movdqu 0xf0(%rsp),%xmm1
    f82d:	c7 82 00 80 ff 7f f1 f1 f1 f1 	movl   $0xf1f1f1f1,0x7fff8000(%rdx)
  return left.tv_sec > right.tv_sec &&
    f837:	48 89 fe             	mov    %rdi,%rsi
int overlap(struct Snapshot left, struct Snapshot right) {
    f83a:	f3 0f 6f 94 24 00 01 00 00 	movdqu 0x100(%rsp),%xmm2
    f843:	c7 82 08 80 ff 7f f2 f2 f2 f2 	movl   $0xf2f2f2f2,0x7fff8008(%rdx)
  return left.tv_sec > right.tv_sec &&
    f84d:	48 c1 ee 03          	shr    $0x3,%rsi
int overlap(struct Snapshot left, struct Snapshot right) {
    f851:	f3 0f 6f 9c 24 10 01 00 00 	movdqu 0x110(%rsp),%xmm3
    f85a:	c7 82 10 80 ff 7f f3 f3 f3 f3 	movl   $0xf3f3f3f3,0x7fff8010(%rdx)
    f864:	f3 0f 6f a4 24 20 01 00 00 	movdqu 0x120(%rsp),%xmm4
    f86d:	64 48 8b 0c 25 28 00 00 00 	mov    %fs:0x28,%rcx
    f876:	48 89 8c 24 b8 00 00 00 	mov    %rcx,0xb8(%rsp)
    f87e:	31 c9                	xor    %ecx,%ecx
  return left.tv_sec > right.tv_sec &&
    f880:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
int overlap(struct Snapshot left, struct Snapshot right) {
    f887:	0f 11 58 a0          	movups %xmm3,-0x60(%rax)
  return left.tv_sec > right.tv_sec &&
    f88b:	48 8d 4b 20          	lea    0x20(%rbx),%rcx
int overlap(struct Snapshot left, struct Snapshot right) {
    f88f:	0f 11 88 60 ff ff ff 	movups %xmm1,-0xa0(%rax)
    f896:	0f 11 90 70 ff ff ff 	movups %xmm2,-0x90(%rax)
    f89d:	0f 11 60 b0          	movups %xmm4,-0x50(%rax)
  return left.tv_sec > right.tv_sec &&
    f8a1:	0f 85 db 01 00 00    	jne    fa82 <overlap+0x2b2>
         left.tv_nsec > right.tv_nsec;
    f8a7:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    f8ab:	4c 8b 90 70 ff ff ff 	mov    -0x90(%rax),%r10
    f8b2:	48 89 fe             	mov    %rdi,%rsi
    f8b5:	48 c1 ee 03          	shr    $0x3,%rsi
    f8b9:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    f8c0:	0f 85 b7 01 00 00    	jne    fa7d <overlap+0x2ad>
  return left.tv_sec > right.tv_sec &&
    f8c6:	48 8d 73 70          	lea    0x70(%rbx),%rsi
    f8ca:	4c 8b 98 78 ff ff ff 	mov    -0x88(%rax),%r11
    f8d1:	48 8d 7b 60          	lea    0x60(%rbx),%rdi
    f8d5:	49 89 f0             	mov    %rsi,%r8
    f8d8:	49 c1 e8 03          	shr    $0x3,%r8
    f8dc:	41 80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r8)
    f8e4:	0f 85 b5 01 00 00    	jne    fa9f <overlap+0x2cf>
         left.tv_nsec > right.tv_nsec;
    f8ea:	48 8d 73 78          	lea    0x78(%rbx),%rsi
    f8ee:	4c 8b 48 b0          	mov    -0x50(%rax),%r9
    f8f2:	49 89 f0             	mov    %rsi,%r8
    f8f5:	49 c1 e8 03          	shr    $0x3,%r8
    f8f9:	41 80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r8)
    f901:	0f 85 90 01 00 00    	jne    fa97 <overlap+0x2c7>
  return left.tv_sec > right.tv_sec &&
    f907:	48 89 ce             	mov    %rcx,%rsi
    f90a:	4c 8b 60 b8          	mov    -0x48(%rax),%r12
    f90e:	48 c1 ee 03          	shr    $0x3,%rsi
    f912:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    f919:	0f 85 70 01 00 00    	jne    fa8f <overlap+0x2bf>
         left.tv_nsec > right.tv_nsec;
    f91f:	48 8d 4b 28          	lea    0x28(%rbx),%rcx
    f923:	4c 8b 80 60 ff ff ff 	mov    -0xa0(%rax),%r8
    f92a:	48 89 ce             	mov    %rcx,%rsi
    f92d:	48 c1 ee 03          	shr    $0x3,%rsi
    f931:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    f938:	0f 85 49 01 00 00    	jne    fa87 <overlap+0x2b7>
  return left.tv_sec > right.tv_sec &&
    f93e:	48 89 f9             	mov    %rdi,%rcx
    f941:	48 8b b0 68 ff ff ff 	mov    -0x98(%rax),%rsi
    f948:	48 c1 e9 03          	shr    $0x3,%rcx
    f94c:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    f953:	0f 85 1f 01 00 00    	jne    fa78 <overlap+0x2a8>
         left.tv_nsec > right.tv_nsec;
    f959:	48 8d 4b 68          	lea    0x68(%rbx),%rcx
    f95d:	48 8b 78 a0          	mov    -0x60(%rax),%rdi
    f961:	49 89 cd             	mov    %rcx,%r13
    f964:	49 c1 ed 03          	shr    $0x3,%r13
    f968:	41 80 bd 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r13)
    f970:	0f 85 fa 00 00 00    	jne    fa70 <overlap+0x2a0>
    f976:	48 8b 48 a8          	mov    -0x58(%rax),%rcx
  return left.tv_sec > right.tv_sec &&
    f97a:	4c 39 c7             	cmp    %r8,%rdi
    f97d:	7d 29                	jge    f9a8 <overlap+0x1d8>
    f97f:	48 39 f1             	cmp    %rsi,%rcx
    f982:	7d 5c                	jge    f9e0 <overlap+0x210>
    f984:	4d 39 e3             	cmp    %r12,%r11
    f987:	7d 0a                	jge    f993 <overlap+0x1c3>
    return 1;
    f989:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    f98e:	4d 39 ca             	cmp    %r9,%r10
    f991:	7c 51                	jl     f9e4 <overlap+0x214>
  return 0;
    f993:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f995:	4d 39 ca             	cmp    %r9,%r10
    f998:	7f 4a                	jg     f9e4 <overlap+0x214>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    f99a:	31 c0                	xor    %eax,%eax
    f99c:	4d 39 e3             	cmp    %r12,%r11
    f99f:	0f 9e c0             	setle  %al
    f9a2:	eb 40                	jmp    f9e4 <overlap+0x214>
    f9a4:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    f9a8:	0f 8e a2 00 00 00    	jle    fa50 <overlap+0x280>
    f9ae:	48 39 f1             	cmp    %rsi,%rcx
    f9b1:	7f 7d                	jg     fa30 <overlap+0x260>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f9b3:	75 2d                	jne    f9e2 <overlap+0x212>
    f9b5:	4d 39 ca             	cmp    %r9,%r10
    f9b8:	7c 28                	jl     f9e2 <overlap+0x212>
    return 1;
    f9ba:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    f9bf:	4d 39 e3             	cmp    %r12,%r11
    f9c2:	7d 20                	jge    f9e4 <overlap+0x214>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    f9c4:	48 39 f1             	cmp    %rsi,%rcx
    f9c7:	0f 94 c1             	sete   %cl
    f9ca:	4c 39 c7             	cmp    %r8,%rdi
    f9cd:	0f 94 c0             	sete   %al
    f9d0:	21 c1                	and    %eax,%ecx
    f9d2:	31 c0                	xor    %eax,%eax
    f9d4:	4d 39 ca             	cmp    %r9,%r10
    f9d7:	0f 94 c0             	sete   %al
    f9da:	21 c8                	and    %ecx,%eax
    f9dc:	eb 06                	jmp    f9e4 <overlap+0x214>
    f9de:	66 90                	xchg   %ax,%ax
    f9e0:	74 b1                	je     f993 <overlap+0x1c3>
  return 0;
    f9e2:	31 c0                	xor    %eax,%eax
int overlap(struct Snapshot left, struct Snapshot right) {
    f9e4:	48 39 dd             	cmp    %rbx,%rbp
    f9e7:	0f 85 ba 00 00 00    	jne    faa7 <overlap+0x2d7>
    f9ed:	c7 82 00 80 ff 7f 00 00 00 00 	movl   $0x0,0x7fff8000(%rdx)
    f9f7:	c7 82 08 80 ff 7f 00 00 00 00 	movl   $0x0,0x7fff8008(%rdx)
    fa01:	c7 82 10 80 ff 7f 00 00 00 00 	movl   $0x0,0x7fff8010(%rdx)
}
    fa0b:	48 8b 94 24 b8 00 00 00 	mov    0xb8(%rsp),%rdx
    fa13:	64 48 2b 14 25 28 00 00 00 	sub    %fs:0x28,%rdx
    fa1c:	0f 85 ca 00 00 00    	jne    faec <overlap+0x31c>
    fa22:	48 81 c4 c8 00 00 00 	add    $0xc8,%rsp
    fa29:	5b                   	pop    %rbx
    fa2a:	5d                   	pop    %rbp
    fa2b:	41 5c                	pop    %r12
    fa2d:	41 5d                	pop    %r13
    fa2f:	c3                   	ret
  return left.tv_sec > right.tv_sec &&
    fa30:	4d 39 e3             	cmp    %r12,%r11
    fa33:	0f 8e 7c ff ff ff    	jle    f9b5 <overlap+0x1e5>
    return 1;
    fa39:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    fa3e:	4d 39 ca             	cmp    %r9,%r10
    fa41:	0f 8e 6e ff ff ff    	jle    f9b5 <overlap+0x1e5>
    fa47:	eb 9b                	jmp    f9e4 <overlap+0x214>
    fa49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    fa50:	48 39 f1             	cmp    %rsi,%rcx
    fa53:	0f 8c 3a ff ff ff    	jl     f993 <overlap+0x1c3>
    fa59:	4d 39 ca             	cmp    %r9,%r10
    fa5c:	0f 8d 58 ff ff ff    	jge    f9ba <overlap+0x1ea>
    fa62:	48 39 f1             	cmp    %rsi,%rcx
    fa65:	0f 84 2f ff ff ff    	je     f99a <overlap+0x1ca>
    fa6b:	e9 72 ff ff ff       	jmp    f9e2 <overlap+0x212>
         left.tv_nsec > right.tv_nsec;
    fa70:	48 89 cf             	mov    %rcx,%rdi
    fa73:	e8 68 4a ff ff       	call   44e0 <__asan_report_load8@plt>
  return left.tv_sec > right.tv_sec &&
    fa78:	e8 63 4a ff ff       	call   44e0 <__asan_report_load8@plt>
         left.tv_nsec > right.tv_nsec;
    fa7d:	e8 5e 4a ff ff       	call   44e0 <__asan_report_load8@plt>
  return left.tv_sec > right.tv_sec &&
    fa82:	e8 59 4a ff ff       	call   44e0 <__asan_report_load8@plt>
         left.tv_nsec > right.tv_nsec;
    fa87:	48 89 cf             	mov    %rcx,%rdi
    fa8a:	e8 51 4a ff ff       	call   44e0 <__asan_report_load8@plt>
  return left.tv_sec > right.tv_sec &&
    fa8f:	48 89 cf             	mov    %rcx,%rdi
    fa92:	e8 49 4a ff ff       	call   44e0 <__asan_report_load8@plt>
         left.tv_nsec > right.tv_nsec;
    fa97:	48 89 f7             	mov    %rsi,%rdi
    fa9a:	e8 41 4a ff ff       	call   44e0 <__asan_report_load8@plt>
  return left.tv_sec > right.tv_sec &&
    fa9f:	48 89 f7             	mov    %rsi,%rdi
    faa2:	e8 39 4a ff ff       	call   44e0 <__asan_report_load8@plt>
int overlap(struct Snapshot left, struct Snapshot right) {
    faa7:	66 0f 6f 05 21 39 00 00 	movdqa 0x3921(%rip),%xmm0        # 133d0 <_IO_stdin_used+0x23d0>
    faaf:	48 c7 03 0e 36 e0 45 	movq   $0x45e0360e,(%rbx)
    fab6:	c7 82 10 80 ff 7f f5 f5 f5 f5 	movl   $0xf5f5f5f5,0x7fff8010(%rdx)
    fac0:	0f 11 82 00 80 ff 7f 	movups %xmm0,0x7fff8000(%rdx)
    fac7:	48 8b 93 f8 00 00 00 	mov    0xf8(%rbx),%rdx
    face:	c6 02 00             	movb   $0x0,(%rdx)
    fad1:	e9 35 ff ff ff       	jmp    fa0b <overlap+0x23b>
    fad6:	bf a0 00 00 00       	mov    $0xa0,%edi
    fadb:	e8 f0 49 ff ff       	call   44d0 <__asan_stack_malloc_2@plt>
    fae0:	48 85 c0             	test   %rax,%rax
    fae3:	48 0f 45 d8          	cmovne %rax,%rbx
    fae7:	e9 09 fd ff ff       	jmp    f7f5 <overlap+0x25>
}
    faec:	e8 bf 4b ff ff       	call   46b0 <__stack_chk_fail@plt>
    faf1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    fafc:	0f 1f 40 00          	nopl   0x0(%rax)

000000000000fb00 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    fb00:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    fb04:	85 f6                	test   %esi,%esi
    fb06:	0f 8e e4 06 00 00    	jle    101f0 <verify+0x6f0>
int verify(struct KernelThread *thread_data, int thread_count) {
    fb0c:	41 57                	push   %r15
    fb0e:	48 89 f8             	mov    %rdi,%rax
    fb11:	41 89 f7             	mov    %esi,%r15d
    fb14:	41 56                	push   %r14
    fb16:	48 83 c0 38          	add    $0x38,%rax
  for (int x = 0 ; x < thread_count; x++) {
    fb1a:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    fb1d:	41 55                	push   %r13
    fb1f:	41 54                	push   %r12
    fb21:	55                   	push   %rbp
    fb22:	53                   	push   %rbx
    fb23:	48 83 ec 78          	sub    $0x78,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    fb27:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    fb2c:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    fb31:	31 db                	xor    %ebx,%ebx
    fb33:	44 89 74 24 4c       	mov    %r14d,0x4c(%rsp)
    fb38:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
      if (z != x)  {
    fb3d:	39 5c 24 4c          	cmp    %ebx,0x4c(%rsp)
    fb41:	0f 84 61 05 00 00    	je     100a8 <verify+0x5a8>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    fb47:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    fb4c:	4c 8d 40 08          	lea    0x8(%rax),%r8
    fb50:	4c 89 c2             	mov    %r8,%rdx
    fb53:	48 c1 ea 03          	shr    $0x3,%rdx
    fb57:	0f b6 92 00 80 ff 7f 	movzbl 0x7fff8000(%rdx),%edx
    fb5e:	84 d2                	test   %dl,%dl
    fb60:	74 09                	je     fb6b <verify+0x6b>
    fb62:	80 fa 03             	cmp    $0x3,%dl
    fb65:	0f 8e 9a 06 00 00    	jle    10205 <verify+0x705>
    fb6b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    fb70:	8b 50 08             	mov    0x8(%rax),%edx
    fb73:	85 d2                	test   %edx,%edx
    fb75:	0f 8e 2d 05 00 00    	jle    100a8 <verify+0x5a8>
    fb7b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    fb80:	89 5c 24 58          	mov    %ebx,0x58(%rsp)
    fb84:	45 31 ed             	xor    %r13d,%r13d
    fb87:	4d 89 c6             	mov    %r8,%r14
    fb8a:	44 89 7c 24 5c       	mov    %r15d,0x5c(%rsp)
    fb8f:	4d 89 e8             	mov    %r13,%r8
    fb92:	4c 8d 60 08          	lea    0x8(%rax),%r12
    fb96:	8b 54 24 4c          	mov    0x4c(%rsp),%edx
    fb9a:	31 c0                	xor    %eax,%eax
    fb9c:	bf 01 00 00 00       	mov    $0x1,%edi
    fba1:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    fba6:	48 8d 35 f3 22 00 00 	lea    0x22f3(%rip),%rsi        # 11ea0 <_IO_stdin_used+0xea0>
    fbad:	e8 6e 49 ff ff       	call   4520 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    fbb2:	4c 89 e0             	mov    %r12,%rax
    fbb5:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    fbba:	48 c1 e8 03          	shr    $0x3,%rax
    fbbe:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
    fbc5:	84 c0                	test   %al,%al
    fbc7:	74 08                	je     fbd1 <verify+0xd1>
    fbc9:	3c 03                	cmp    $0x3,%al
    fbcb:	0f 8e 22 06 00 00    	jle    101f3 <verify+0x6f3>
    fbd1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    fbd6:	8b 40 08             	mov    0x8(%rax),%eax
    fbd9:	85 c0                	test   %eax,%eax
    fbdb:	0f 8e 91 04 00 00    	jle    10072 <verify+0x572>
    fbe1:	4c 89 c0             	mov    %r8,%rax
    fbe4:	48 c1 e0 09          	shl    $0x9,%rax
    fbe8:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    fbed:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    fbf2:	48 c1 e8 03          	shr    $0x3,%rax
    fbf6:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fbfd:	0f 85 f8 05 00 00    	jne    101fb <verify+0x6fb>
    fc03:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    fc08:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
    fc0d:	4c 89 74 24 60       	mov    %r14,0x60(%rsp)
    fc12:	31 db                	xor    %ebx,%ebx
    fc14:	4c 89 44 24 68       	mov    %r8,0x68(%rsp)
    fc19:	48 03 28             	add    (%rax),%rbp
    fc1c:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    fc21:	4c 89 64 24 40       	mov    %r12,0x40(%rsp)
    fc26:	48 c1 e8 03          	shr    $0x3,%rax
    fc2a:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    fc2f:	90                   	nop
    fc30:	48 8d bd 60 01 00 00 	lea    0x160(%rbp),%rdi
    fc37:	48 89 f8             	mov    %rdi,%rax
    fc3a:	48 c1 e8 03          	shr    $0x3,%rax
    fc3e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fc45:	0f 85 2c 05 00 00    	jne    10177 <verify+0x677>
    fc4b:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    fc50:	48 8b 8d 60 01 00 00 	mov    0x160(%rbp),%rcx
    fc57:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fc5e:	0f 85 5f 05 00 00    	jne    101c3 <verify+0x6c3>
    fc64:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    fc69:	48 89 d8             	mov    %rbx,%rax
    fc6c:	48 c1 e0 09          	shl    $0x9,%rax
    fc70:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    fc75:	48 03 06             	add    (%rsi),%rax
    fc78:	48 8d b8 60 01 00 00 	lea    0x160(%rax),%rdi
    fc7f:	48 89 fa             	mov    %rdi,%rdx
    fc82:	48 c1 ea 03          	shr    $0x3,%rdx
    fc86:	80 ba 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rdx)
    fc8d:	0f 85 2b 05 00 00    	jne    101be <verify+0x6be>
    fc93:	48 8b 90 60 01 00 00 	mov    0x160(%rax),%rdx
    fc9a:	48 8d 35 3f 22 00 00 	lea    0x223f(%rip),%rsi        # 11ee0 <_IO_stdin_used+0xee0>
    fca1:	31 c0                	xor    %eax,%eax
    fca3:	bf 01 00 00 00       	mov    $0x1,%edi
    fca8:	e8 73 48 ff ff       	call   4520 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    fcad:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    fcb2:	48 c1 e8 03          	shr    $0x3,%rax
    fcb6:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fcbd:	0f 85 0a 05 00 00    	jne    101cd <verify+0x6cd>
    fcc3:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    fcc8:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
    fccd:	48 03 28             	add    (%rax),%rbp
    fcd0:	48 8d bd 60 01 00 00 	lea    0x160(%rbp),%rdi
    fcd7:	48 89 f8             	mov    %rdi,%rax
    fcda:	48 c1 e8 03          	shr    $0x3,%rax
    fcde:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fce5:	0f 85 ce 04 00 00    	jne    101b9 <verify+0x6b9>
    fceb:	48 8b 85 60 01 00 00 	mov    0x160(%rbp),%rax
    fcf2:	48 85 c0             	test   %rax,%rax
    fcf5:	0f 8e 3a 03 00 00    	jle    10035 <verify+0x535>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    fcfb:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    fd00:	80 be 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rsi)
    fd07:	0f 85 6f 04 00 00    	jne    1017c <verify+0x67c>
    fd0d:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    fd12:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
    fd17:	48 89 5c 24 38       	mov    %rbx,0x38(%rsp)
    fd1c:	41 bd 01 00 00 00    	mov    $0x1,%r13d
    fd22:	48 03 16             	add    (%rsi),%rdx
    fd25:	0f 1f 00             	nopl   (%rax)
    fd28:	48 8d ba 60 01 00 00 	lea    0x160(%rdx),%rdi
    fd2f:	48 89 f9             	mov    %rdi,%rcx
    fd32:	48 c1 e9 03          	shr    $0x3,%rcx
    fd36:	80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rcx)
    fd3d:	0f 85 4d 04 00 00    	jne    10190 <verify+0x690>
    fd43:	4c 8b b2 60 01 00 00 	mov    0x160(%rdx),%r14
    fd4a:	4d 85 f6             	test   %r14,%r14
    fd4d:	0f 8e 75 03 00 00    	jle    100c8 <verify+0x5c8>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    fd53:	4d 89 ec             	mov    %r13,%r12
    fd56:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
    fd5b:	31 db                	xor    %ebx,%ebx
    fd5d:	49 c1 e4 05          	shl    $0x5,%r12
    fd61:	49 83 ec 20          	sub    $0x20,%r12
    fd65:	eb 36                	jmp    fd9d <verify+0x29d>
    fd67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    fd70:	4c 39 c1             	cmp    %r8,%rcx
    fd73:	0f 8d 57 02 00 00    	jge    ffd0 <verify+0x4d0>
    fd79:	4d 39 cd             	cmp    %r9,%r13
    fd7c:	7d 09                	jge    fd87 <verify+0x287>
    fd7e:	4d 39 da             	cmp    %r11,%r10
    fd81:	0f 8f 89 01 00 00    	jg     ff10 <verify+0x410>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    fd87:	4d 39 da             	cmp    %r11,%r10
    fd8a:	0f 8d 8b 02 00 00    	jge    1001b <verify+0x51b>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    fd90:	48 83 c3 01          	add    $0x1,%rbx
    fd94:	49 39 de             	cmp    %rbx,%r14
    fd97:	0f 8e fd 01 00 00    	jle    ff9a <verify+0x49a>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    fd9d:	48 8d ba 50 01 00 00 	lea    0x150(%rdx),%rdi
    fda4:	48 89 f8             	mov    %rdi,%rax
    fda7:	48 c1 e8 03          	shr    $0x3,%rax
    fdab:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fdb2:	0f 85 9c 03 00 00    	jne    10154 <verify+0x654>
    fdb8:	48 8d bd 50 01 00 00 	lea    0x150(%rbp),%rdi
    fdbf:	49 89 df             	mov    %rbx,%r15
    fdc2:	48 89 f8             	mov    %rdi,%rax
    fdc5:	49 c1 e7 05          	shl    $0x5,%r15
    fdc9:	4c 03 ba 50 01 00 00 	add    0x150(%rdx),%r15
    fdd0:	48 c1 e8 03          	shr    $0x3,%rax
    fdd4:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fddb:	0f 85 6e 03 00 00    	jne    1014f <verify+0x64f>
    fde1:	48 8b bd 50 01 00 00 	mov    0x150(%rbp),%rdi
    fde8:	4c 01 e7             	add    %r12,%rdi
  return left.tv_sec > right.tv_sec &&
    fdeb:	48 89 f8             	mov    %rdi,%rax
    fdee:	48 c1 e8 03          	shr    $0x3,%rax
    fdf2:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fdf9:	0f 85 4b 03 00 00    	jne    1014a <verify+0x64a>
         left.tv_nsec > right.tv_nsec;
    fdff:	48 8d 4f 08          	lea    0x8(%rdi),%rcx
    fe03:	48 8b 37             	mov    (%rdi),%rsi
    fe06:	48 89 c8             	mov    %rcx,%rax
    fe09:	48 c1 e8 03          	shr    $0x3,%rax
    fe0d:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fe14:	0f 85 28 03 00 00    	jne    10142 <verify+0x642>
  return left.tv_sec > right.tv_sec &&
    fe1a:	48 8d 4f 10          	lea    0x10(%rdi),%rcx
    fe1e:	4c 8b 47 08          	mov    0x8(%rdi),%r8
    fe22:	48 89 c8             	mov    %rcx,%rax
    fe25:	48 c1 e8 03          	shr    $0x3,%rax
    fe29:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fe30:	0f 85 04 03 00 00    	jne    1013a <verify+0x63a>
         left.tv_nsec > right.tv_nsec;
    fe36:	48 8d 4f 18          	lea    0x18(%rdi),%rcx
    fe3a:	4c 8b 5f 10          	mov    0x10(%rdi),%r11
    fe3e:	48 89 c8             	mov    %rcx,%rax
    fe41:	48 c1 e8 03          	shr    $0x3,%rax
    fe45:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fe4c:	0f 85 e0 02 00 00    	jne    10132 <verify+0x632>
  return left.tv_sec > right.tv_sec &&
    fe52:	4c 89 f8             	mov    %r15,%rax
    fe55:	4c 8b 6f 18          	mov    0x18(%rdi),%r13
    fe59:	48 c1 e8 03          	shr    $0x3,%rax
    fe5d:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fe64:	0f 85 c0 02 00 00    	jne    1012a <verify+0x62a>
         left.tv_nsec > right.tv_nsec;
    fe6a:	4d 8d 4f 08          	lea    0x8(%r15),%r9
    fe6e:	49 8b 3f             	mov    (%r15),%rdi
    fe71:	4c 89 c8             	mov    %r9,%rax
    fe74:	48 c1 e8 03          	shr    $0x3,%rax
    fe78:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fe7f:	0f 85 9d 02 00 00    	jne    10122 <verify+0x622>
  return left.tv_sec > right.tv_sec &&
    fe85:	4d 8d 57 10          	lea    0x10(%r15),%r10
    fe89:	49 8b 4f 08          	mov    0x8(%r15),%rcx
    fe8d:	4c 89 d0             	mov    %r10,%rax
    fe90:	48 c1 e8 03          	shr    $0x3,%rax
    fe94:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    fe9b:	0f 85 79 02 00 00    	jne    1011a <verify+0x61a>
         left.tv_nsec > right.tv_nsec;
    fea1:	49 8d 47 18          	lea    0x18(%r15),%rax
    fea5:	4d 8b 57 10          	mov    0x10(%r15),%r10
    fea9:	49 89 c1             	mov    %rax,%r9
    feac:	49 c1 e9 03          	shr    $0x3,%r9
    feb0:	41 80 b9 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%r9)
    feb8:	0f 85 54 02 00 00    	jne    10112 <verify+0x612>
    febe:	4d 8b 4f 18          	mov    0x18(%r15),%r9
  return left.tv_sec > right.tv_sec &&
    fec2:	48 39 f7             	cmp    %rsi,%rdi
    fec5:	0f 8c a5 fe ff ff    	jl     fd70 <verify+0x270>
    fecb:	0f 8e 2f 01 00 00    	jle    10000 <verify+0x500>
    fed1:	4c 39 c1             	cmp    %r8,%rcx
    fed4:	0f 8f 06 01 00 00    	jg     ffe0 <verify+0x4e0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    feda:	0f 85 b0 fe ff ff    	jne    fd90 <verify+0x290>
    fee0:	4d 39 da             	cmp    %r11,%r10
    fee3:	0f 8f a7 fe ff ff    	jg     fd90 <verify+0x290>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    fee9:	4d 39 cd             	cmp    %r9,%r13
    feec:	7d 22                	jge    ff10 <verify+0x410>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    feee:	4c 39 c1             	cmp    %r8,%rcx
    fef1:	0f 94 c1             	sete   %cl
    fef4:	48 39 f7             	cmp    %rsi,%rdi
    fef7:	0f 94 c0             	sete   %al
    fefa:	84 c1                	test   %al,%cl
    fefc:	0f 84 8e fe ff ff    	je     fd90 <verify+0x290>
    ff02:	4d 39 da             	cmp    %r11,%r10
    ff05:	0f 85 85 fe ff ff    	jne    fd90 <verify+0x290>
    ff0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    ff10:	48 89 f2             	mov    %rsi,%rdx
    ff13:	31 c0                	xor    %eax,%eax
    ff15:	4c 89 d1             	mov    %r10,%rcx
    ff18:	bf 01 00 00 00       	mov    $0x1,%edi
    ff1d:	48 8d 35 fc 1f 00 00 	lea    0x1ffc(%rip),%rsi        # 11f20 <_IO_stdin_used+0xf20>
    ff24:	e8 f7 45 ff ff       	call   4520 <__printf_chk@plt>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    ff29:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    ff2e:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ff35:	0f 85 2d 02 00 00    	jne    10168 <verify+0x668>
    ff3b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    ff40:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
    ff45:	48 03 10             	add    (%rax),%rdx
    ff48:	48 8d ba 60 01 00 00 	lea    0x160(%rdx),%rdi
    ff4f:	48 89 f8             	mov    %rdi,%rax
    ff52:	48 c1 e8 03          	shr    $0x3,%rax
    ff56:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ff5d:	0f 85 00 02 00 00    	jne    10163 <verify+0x663>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    ff63:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    ff68:	4c 8b b2 60 01 00 00 	mov    0x160(%rdx),%r14
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    ff6f:	48 c1 e8 03          	shr    $0x3,%rax
    ff73:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ff7a:	0f 85 d9 01 00 00    	jne    10159 <verify+0x659>
    ff80:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    ff85:	48 83 c3 01          	add    $0x1,%rbx
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    ff89:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
    ff8e:	48 03 28             	add    (%rax),%rbp
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    ff91:	49 39 de             	cmp    %rbx,%r14
    ff94:	0f 8f 03 fe ff ff    	jg     fd9d <verify+0x29d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    ff9a:	48 8d bd 60 01 00 00 	lea    0x160(%rbp),%rdi
    ffa1:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
    ffa6:	48 89 f8             	mov    %rdi,%rax
    ffa9:	48 c1 e8 03          	shr    $0x3,%rax
    ffad:	80 b8 00 80 ff 7f 00 	cmpb   $0x0,0x7fff8000(%rax)
    ffb4:	0f 85 b8 01 00 00    	jne    10172 <verify+0x672>
    ffba:	48 8b 85 60 01 00 00 	mov    0x160(%rbp),%rax
    ffc1:	49 39 c5             	cmp    %rax,%r13
    ffc4:	7d 6a                	jge    10030 <verify+0x530>
    ffc6:	49 83 c5 01          	add    $0x1,%r13
    ffca:	e9 59 fd ff ff       	jmp    fd28 <verify+0x228>
    ffcf:	90                   	nop
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    ffd0:	0f 85 ba fd ff ff    	jne    fd90 <verify+0x290>
    ffd6:	e9 ac fd ff ff       	jmp    fd87 <verify+0x287>
    ffdb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    ffe0:	4d 39 cd             	cmp    %r9,%r13
    ffe3:	0f 8e f7 fe ff ff    	jle    fee0 <verify+0x3e0>
    ffe9:	4d 39 da             	cmp    %r11,%r10
    ffec:	0f 8d ee fe ff ff    	jge    fee0 <verify+0x3e0>
    fff2:	e9 19 ff ff ff       	jmp    ff10 <verify+0x410>
    fff7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
   10000:	4c 39 c1             	cmp    %r8,%rcx
   10003:	0f 8c 7e fd ff ff    	jl     fd87 <verify+0x287>
   10009:	4d 39 da             	cmp    %r11,%r10
   1000c:	0f 8e d7 fe ff ff    	jle    fee9 <verify+0x3e9>
   10012:	4c 39 c1             	cmp    %r8,%rcx
   10015:	0f 85 75 fd ff ff    	jne    fd90 <verify+0x290>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
   1001b:	4d 39 cd             	cmp    %r9,%r13
   1001e:	0f 8f 6c fd ff ff    	jg     fd90 <verify+0x290>
   10024:	e9 e7 fe ff ff       	jmp    ff10 <verify+0x410>
   10029:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
   10030:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
   10035:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
   1003a:	48 c1 e8 03          	shr    $0x3,%rax
   1003e:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
   10045:	84 c0                	test   %al,%al
   10047:	74 08                	je     10051 <verify+0x551>
   10049:	3c 03                	cmp    $0x3,%al
   1004b:	0f 8e 35 01 00 00    	jle    10186 <verify+0x686>
   10051:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
   10056:	48 83 c3 01          	add    $0x1,%rbx
   1005a:	39 58 08             	cmp    %ebx,0x8(%rax)
   1005d:	0f 8f cd fb ff ff    	jg     fc30 <verify+0x130>
   10063:	4c 8b 74 24 60       	mov    0x60(%rsp),%r14
   10068:	4c 8b 44 24 68       	mov    0x68(%rsp),%r8
   1006d:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
   10072:	4c 89 f0             	mov    %r14,%rax
   10075:	48 c1 e8 03          	shr    $0x3,%rax
   10079:	0f b6 80 00 80 ff 7f 	movzbl 0x7fff8000(%rax),%eax
   10080:	84 c0                	test   %al,%al
   10082:	74 08                	je     1008c <verify+0x58c>
   10084:	3c 03                	cmp    $0x3,%al
   10086:	0f 8e 5c 01 00 00    	jle    101e8 <verify+0x6e8>
   1008c:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
   10091:	49 83 c0 01          	add    $0x1,%r8
   10095:	44 39 40 08          	cmp    %r8d,0x8(%rax)
   10099:	0f 8f f7 fa ff ff    	jg     fb96 <verify+0x96>
   1009f:	8b 5c 24 58          	mov    0x58(%rsp),%ebx
   100a3:	44 8b 7c 24 5c       	mov    0x5c(%rsp),%r15d
    for (int z = 0 ; z < thread_count; z++) {
   100a8:	48 81 44 24 10 c0 00 00 00 	addq   $0xc0,0x10(%rsp)
   100b1:	8d 53 01             	lea    0x1(%rbx),%edx
   100b4:	41 39 d7             	cmp    %edx,%r15d
   100b7:	0f 84 d8 00 00 00    	je     10195 <verify+0x695>
   100bd:	89 d3                	mov    %edx,%ebx
   100bf:	e9 79 fa ff ff       	jmp    fb3d <verify+0x3d>
   100c4:	0f 1f 40 00          	nopl   0x0(%rax)
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
   100c8:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
   100cd:	4c 39 e8             	cmp    %r13,%rax
   100d0:	0f 8e 5f ff ff ff    	jle    10035 <verify+0x535>
   100d6:	4d 63 ed             	movslq %r13d,%r13
   100d9:	4c 89 ea             	mov    %r13,%rdx
   100dc:	49 83 c5 01          	add    $0x1,%r13
   100e0:	48 f7 d2             	not    %rdx
   100e3:	48 01 c2             	add    %rax,%rdx
   100e6:	83 e2 01             	and    $0x1,%edx
   100e9:	4c 39 e8             	cmp    %r13,%rax
   100ec:	0f 8e 43 ff ff ff    	jle    10035 <verify+0x535>
   100f2:	48 85 d2             	test   %rdx,%rdx
   100f5:	74 0d                	je     10104 <verify+0x604>
   100f7:	49 83 c5 01          	add    $0x1,%r13
   100fb:	4c 39 e8             	cmp    %r13,%rax
   100fe:	0f 8e 31 ff ff ff    	jle    10035 <verify+0x535>
   10104:	49 83 c5 02          	add    $0x2,%r13
   10108:	4c 39 e8             	cmp    %r13,%rax
   1010b:	7f f7                	jg     10104 <verify+0x604>
   1010d:	e9 23 ff ff ff       	jmp    10035 <verify+0x535>
         left.tv_nsec > right.tv_nsec;
   10112:	48 89 c7             	mov    %rax,%rdi
   10115:	e8 c6 43 ff ff       	call   44e0 <__asan_report_load8@plt>
  return left.tv_sec > right.tv_sec &&
   1011a:	4c 89 d7             	mov    %r10,%rdi
   1011d:	e8 be 43 ff ff       	call   44e0 <__asan_report_load8@plt>
         left.tv_nsec > right.tv_nsec;
   10122:	4c 89 cf             	mov    %r9,%rdi
   10125:	e8 b6 43 ff ff       	call   44e0 <__asan_report_load8@plt>
  return left.tv_sec > right.tv_sec &&
   1012a:	4c 89 ff             	mov    %r15,%rdi
   1012d:	e8 ae 43 ff ff       	call   44e0 <__asan_report_load8@plt>
         left.tv_nsec > right.tv_nsec;
   10132:	48 89 cf             	mov    %rcx,%rdi
   10135:	e8 a6 43 ff ff       	call   44e0 <__asan_report_load8@plt>
  return left.tv_sec > right.tv_sec &&
   1013a:	48 89 cf             	mov    %rcx,%rdi
   1013d:	e8 9e 43 ff ff       	call   44e0 <__asan_report_load8@plt>
         left.tv_nsec > right.tv_nsec;
   10142:	48 89 cf             	mov    %rcx,%rdi
   10145:	e8 96 43 ff ff       	call   44e0 <__asan_report_load8@plt>
  return left.tv_sec > right.tv_sec &&
   1014a:	e8 91 43 ff ff       	call   44e0 <__asan_report_load8@plt>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
   1014f:	e8 8c 43 ff ff       	call   44e0 <__asan_report_load8@plt>
   10154:	e8 87 43 ff ff       	call   44e0 <__asan_report_load8@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
   10159:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
   1015e:	e8 7d 43 ff ff       	call   44e0 <__asan_report_load8@plt>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
   10163:	e8 78 43 ff ff       	call   44e0 <__asan_report_load8@plt>
   10168:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
   1016d:	e8 6e 43 ff ff       	call   44e0 <__asan_report_load8@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
   10172:	e8 69 43 ff ff       	call   44e0 <__asan_report_load8@plt>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
   10177:	e8 64 43 ff ff       	call   44e0 <__asan_report_load8@plt>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
   1017c:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
   10181:	e8 5a 43 ff ff       	call   44e0 <__asan_report_load8@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
   10186:	48 8b 7c 24 40       	mov    0x40(%rsp),%rdi
   1018b:	e8 c0 43 ff ff       	call   4550 <__asan_report_load4@plt>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
   10190:	e8 4b 43 ff ff       	call   44e0 <__asan_report_load8@plt>
   10195:	44 8b 74 24 4c       	mov    0x4c(%rsp),%r14d
   1019a:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
  for (int x = 0 ; x < thread_count; x++) {
   1019f:	48 81 44 24 08 c0 00 00 00 	addq   $0xc0,0x8(%rsp)
   101a8:	41 8d 56 01          	lea    0x1(%r14),%edx
   101ac:	41 39 de             	cmp    %ebx,%r14d
   101af:	74 26                	je     101d7 <verify+0x6d7>
   101b1:	41 89 d6             	mov    %edx,%r14d
   101b4:	e9 73 f9 ff ff       	jmp    fb2c <verify+0x2c>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
   101b9:	e8 22 43 ff ff       	call   44e0 <__asan_report_load8@plt>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
   101be:	e8 1d 43 ff ff       	call   44e0 <__asan_report_load8@plt>
   101c3:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
   101c8:	e8 13 43 ff ff       	call   44e0 <__asan_report_load8@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
   101cd:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
   101d2:	e8 09 43 ff ff       	call   44e0 <__asan_report_load8@plt>
}
   101d7:	48 83 c4 78          	add    $0x78,%rsp
   101db:	31 c0                	xor    %eax,%eax
   101dd:	5b                   	pop    %rbx
   101de:	5d                   	pop    %rbp
   101df:	41 5c                	pop    %r12
   101e1:	41 5d                	pop    %r13
   101e3:	41 5e                	pop    %r14
   101e5:	41 5f                	pop    %r15
   101e7:	c3                   	ret
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
   101e8:	4c 89 f7             	mov    %r14,%rdi
   101eb:	e8 60 43 ff ff       	call   4550 <__asan_report_load4@plt>
}
   101f0:	31 c0                	xor    %eax,%eax
   101f2:	c3                   	ret
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
   101f3:	4c 89 e7             	mov    %r12,%rdi
   101f6:	e8 55 43 ff ff       	call   4550 <__asan_report_load4@plt>
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
   101fb:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
   10200:	e8 db 42 ff ff       	call   44e0 <__asan_report_load8@plt>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
   10205:	4c 89 c7             	mov    %r8,%rdi
   10208:	e8 43 43 ff ff       	call   4550 <__asan_report_load4@plt>

Disassembly of section .fini:

0000000000010210 <_fini>:
   10210:	f3 0f 1e fa          	endbr64
   10214:	48 83 ec 08          	sub    $0x8,%rsp
   10218:	48 83 c4 08          	add    $0x8,%rsp
   1021c:	c3                   	ret
