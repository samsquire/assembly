# multithreaded nonblocking barrier-runtime

This repository has:

 * a nonblocking barrier runtime: no mutexes in C
 * an LMAX Disruptor inspired ringbuffer in C
 * a [simple summary](https://github.com/samsquire/assembly/blob/main/assembly/README.md) of what I've learned programming in assembly
 * Marce Coll's tweaked coroutines assembly coroutinesdirect.S

|File|Description|
|---|---|
|disruptor-multi.c|1 writer thread and 2 consumer threads|
|disruptor-multi-producer|2 producer threads and 1 consumer threads. This is not thread safe yet.|
|disruptor-multi-consumer|2 producer threads and 2 consumer threads. I have attempted to make this thread safe but I need to think on it longer.|



# nonblocking-prearrive

This is my [Samuel Michael Squire](https://samsquire.com/), sam@samsquire.com) lock free algorithm and runtime for a nonblocking multithreaded barrier. It is Zero Clause BSD Licenced.

```
Total Requests 27317816286

Total Protected 63025917
Total V 63025917

Total Protected per second 2100863
Total money 500 (correct if 0 or 500)
Total external thread ingests per second 2691622
Total intra thread sends per second 409855901
Total Requests per second 910593876
Total sents 409855901
Total receives 40985590
```

With 12 threads for 30 seconds, 10 threads all incrementing a long can do all the following: 910 million additions, 409 million interthread sends, 2.6 million external thread ingests and 2.1 million critical sections a second.

On a Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz, 1608 Mhz, 6 Core(s), 12 Logical Processor(s) CPU on Windows 11 Intel NUC inside an Lubuntu virtual machine.

This algorithm is inspired by [Bulk synchronous parallel](https://en.wikipedia.org/wiki/Bulk_Synchronous_Parallel).

This algorithm uses ideas from my **M:N** thread scheduler, which is at [samsquire/preemptible-thread](https://github.com/samsquire/preemptible-thread).

In Go, if you are sending 64 bits of data to a channel, this causes unnecessary context switches in the go scheduler.

This algorithm is based on the idea there is a timeline grid of work to do and we synchronise in bulk on an interval. For the vast majority of time every thread is doing useful work, and synchronization is **total synchronization** between all threads in the cluster. Each thread has its own collection of **supersteps called BarrierTasks**. Each thread can do a different task in eachstep.

When the `BarrierTask.task_index == BarrierTask.thread_index`, we are guaranteed to be the only thread executing this code. This is similar to a critical section or a mutex. The great thing about this algorithm is that we can synchronize and do data transfer in bulk.

This barrier creates the following rhythm. The threads can arrive in any order, but they **do not start the next superstep** until they have all sycnhronized the previous superstep.

```
8 Arrived at task 0
5 Arrived at task 0
2 Arrived at task 0
6 Arrived at task 0
3 Arrived at task 0
4 Arrived at task 0
7 Arrived at task 0
0 Arrived at task 0
1 Arrived at task 0
9 Arrived at task 0
9 Arrived at task 1
3 Arrived at task 1
4 Arrived at task 1
8 Arrived at task 1
7 Arrived at task 1
5 Arrived at task 1
6 Arrived at task 1
1 Arrived at task 1
2 Arrived at task 1
0 Arrived at task 1
5 Arrived at task 2
6 Arrived at task 2
0 Arrived at task 2
1 Arrived at task 2
8 Arrived at task 2
7 Arrived at task 2
9 Arrived at task 2
2 Arrived at task 2
3 Arrived at task 2
4 Arrived at task 2
4 Arrived at task 3
7 Arrived at task 3
3 Arrived at task 3
9 Arrived at task 3
6 Arrived at task 3
8 Arrived at task 3
5 Arrived at task 3
1 Arrived at task 3
2 Arrived at task 3
0 Arrived at task 3
4 Arrived at task 4
8 Arrived at task 4
1 Arrived at task 4
5 Arrived at task 4
7 Arrived at task 4
6 Arrived at task 4
2 Arrived at task 4
9 Arrived at task 4
0 Arrived at task 4
3 Arrived at task 4
3 Arrived at task 5
5 Arrived at task 5
9 Arrived at task 5
6 Arrived at task 5
7 Arrived at task 5
8 Arrived at task 5
4 Arrived at task 5
0 Arrived at task 5
1 Arrived at task 5
2 Arrived at task 5
4 Arrived at task 6
2 Arrived at task 6
7 Arrived at task 6
6 Arrived at task 6
8 Arrived at task 6
5 Arrived at task 6
3 Arrived at task 6
9 Arrived at task 6
0 Arrived at task 6
1 Arrived at task 6
4 Arrived at task 7
9 Arrived at task 7
5 Arrived at task 7
7 Arrived at task 7
3 Arrived at task 7
6 Arrived at task 7
8 Arrived at task 7
2 Arrived at task 7
1 Arrived at task 7
0 Arrived at task 7
3 Arrived at task 8
5 Arrived at task 8
6 Arrived at task 8
2 Arrived at task 8
4 Arrived at task 8
7 Arrived at task 8
8 Arrived at task 8
1 Arrived at task 8
9 Arrived at task 8
0 Arrived at task 8

```

See [volatile considered harmful](https://www.kernel.org/doc/html/latest/process/volatile-considered-harmful.html).

These algorithms use memory barriers and happens before relationships. I take advantage of benign data races. **If you use atomics, the program is slow**. There is a whitepaper called ["How to miscompile programs with “benign” data races"](https://www.usenix.org/legacy/events/hotpar11/tech/final_files/Boehm.pdf) There are errors reported by Thread Sanitizer. There is a **happens before** relationship between **arrived** and writes to arrived always **come from the same thread**. If they are observed by another thread the value is stale, it doesn't **seem** to affect correctness.



# THROUGHPUT vs LATENCY

LMAX Disruptor can transmit a message between threads with average latency of 53 nanoseconds.

This assumes there is a thread busy spinning on a sequence number and waiting for it to become available when another thread (a producer) has written it.

The `multibarrier-prearrive` latencies:


```
2 tasks (1) synchronized in 0 seconds 0 milliseconds 42 nanoseconds
2 tasks (2) synchronized in 0 seconds 0 milliseconds 51 nanoseconds
2 tasks (0) synchronized in 0 seconds 0 milliseconds 42 nanoseconds
2 tasks (1) synchronized in 0 seconds 0 milliseconds 42 nanoseconds
2 tasks (2) synchronized in 0 seconds 0 milliseconds 49 nanoseconds
2 tasks (0) synchronized in 0 seconds 0 milliseconds 45 nanoseconds
2 tasks (1) synchronized in 0 seconds 0 milliseconds 42 nanoseconds
2 tasks (2) synchronized in 0 seconds 0 milliseconds 48 nanoseconds
2 tasks (0) synchronized in 0 seconds 0 milliseconds 45 nanoseconds
2 tasks (1) synchronized in 0 seconds 0 milliseconds 43 nanoseconds
2 tasks (2) synchronized in 0 seconds 0 milliseconds 46 nanoseconds
2 tasks (0) synchronized in 0 seconds 0 milliseconds 41 nanoseconds
2 tasks (1) synchronized in 0 seconds 0 milliseconds 44 nanoseconds
2 tasks (2) synchronized in 0 seconds 0 milliseconds 46 nanoseconds
2 tasks (0) synchronized in 0 seconds 0 milliseconds 48 nanoseconds
2 tasks (1) synchronized in 0 seconds 0 milliseconds 44 nanoseconds
2 tasks (2) synchronized in 0 seconds 0 milliseconds 45 nanoseconds
2 tasks (0) synchronized in 0 seconds 0 milliseconds 45 nanoseconds
2 tasks (1) synchronized in 0 seconds 0 milliseconds 48 nanoseconds
2 tasks (2) synchronized in 0 seconds 0 milliseconds 51 nanoseconds
2 tasks (0) synchronized in 0 seconds 0 milliseconds 40 nanoseconds
```



# how it works

If you imagine a 2 dimensional table or grid with **workers (threads) that are rows** and **tasks that are columns**, the identity matrix is a row and column in that grid that if the task index is equal to the worker (thread) index then there is nobody else executing that: you get mutual exclusion. It is diagonal line through the grid over time.

```
void* barriered_thread(void *arg) {
  struct KernelThread *data = arg;
  // printf("In barrier task %d\n", data->thread_index);
  int t = 0;
  while (data->running == 1) {
    if (t >= data->task_count) {
      t = 0;
    }
    // printf("%d reporting %d %d\n", data->thread_index, t, data->task_count);
    for (; t < data->task_count; t++) {
      // printf("%d %d\n", data->thread_index, t);
      if (data->tasks[t].available == 1) {
        int previous = t;
        if (t > 0) {
          previous = t - 1;
        } else {
          previous = data->task_count - 1;
        }
        int arrived = 0; 
        for (int thread = 0 ; thread < data->thread_count; thread++) {
          // printf("thread %d does %d %d %d == %d\n", data->thread_index, t, previous, data->threads[thread].tasks[previous].arrived, data->tasks[t].arrived);
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
            arrived++;
          } 
        } 
        if (arrived == 0 || arrived == data->thread_count) {
          // we can run this task

          data->tasks[t].available = 0;

          data->tasks[t].run(&data->threads[data->thread_index].tasks[t]);
          data->tasks[t].arrived++;
          asm volatile ("mfence" ::: "memory");
        } else {
          // printf("%d %d %d\n", data->thread_index, t, arrived);
          break;
        }   
      } else {
      }
    }
  } 
  return 0;
}
```

This is what the work task looks like:

```
int barriered_work(volatile struct BarrierTask *data) {
  // printf("In barrier work task %d %d\n", data->thread_index, data->task_index);
  // printf("%d Arrived at task %d\n", data->thread_index, data->task_index);
  volatile long *n = &data->n;
  char *message = malloc(sizeof(char) * 256);
  struct Message *messaged = malloc(sizeof(struct Message));
  memset(message, '\0', 256);
  sprintf(message, "Sending message from thread %d task %d", data->thread_index, data->task_index);
  messaged->message = message;
  messaged->task_index = data->task_index;
  messaged->thread_index = data->thread_index;
  // we are synchronized
  if (data->thread_index == data->task_index) {
      void * tmp; 
      // swap this all thread's write buffer with the next task
        int t = data->task_index;
        for (int y = 0; y < data->thread_count ; y++) {
          for (int b = 0; b < data->thread_count ; b++) {
              int next_task = abs((t + 1) % (data->task_count));
              tmp = data->thread->threads[y].tasks[t].mailboxes[b].higher; 
              // data->thread->threads[y].tasks[t].mailboxes[b].higher = data->thread->threads[b].tasks[next_task].mailboxes[y].lower;
              data->thread->threads[b].tasks[next_task].mailboxes[y].lower = tmp;
            }
        }
      asm volatile ("mfence" ::: "memory");
        // printf("move my %d lower to next %d lower\n",data->task_index, next_task);


    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    int modcount = ++data->thread->protected_state->modcount;
    while (data->scheduled == 1) {
      data->n++;
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
    }
    if (modcount != data->thread->protected_state->modcount) {
      printf("Race condition!\n");
    }
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
  } else {
        for (int n = 0 ; n < data->thread_count; n++) {
          if (n == data->thread_index) { continue; }
          struct Data *me = data->mailboxes[n].lower;
          for (int x = 0 ; x < me->messages_count ; x++) {
            data->sends++;
            // printf("on %d from %d task %d received: %s\n", data->thread_index, n, data->task_index, me->messages[x]->message);
            if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
              printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread_index);
              exit(1);
            }
          }
          me->messages_count = 0;
      }
        while (data->scheduled == 1) {
          for (int n = 0 ; n < data->thread_count; n++) {
            if (n == data->thread_index) { continue; }
            struct Data *them = data->mailboxes[n].higher;
            data->n++;
            // printf("Sending to thread %d\n", n);
            if (them->messages_count < them->messages_limit) {
              them->messages[them->messages_count++] = messaged;
            }
          }
        }
      asm volatile ("mfence" ::: "memory");
  }
  return 0;
}
```


This is what happens when all tasks are finished:

```
int barriered_reset(volatile struct BarrierTask *data) {
  // printf("In barrier reset task %d %d\n", data->thread_index, data->task_index);
    for (int x = 0 ; x < data->task_count ; x++) {
      // printf("Resetting %d %d\n", n, x);
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
      // data->thread->tasks[x].arrived++; 
      
      data->thread->tasks[x].available = 1; 
  }
  asm volatile ("mfence" ::: "memory");
  return 0;
}
```

# external thread ingest

The multithreaded barrier can ingest events from an external thread, which is slower than running internal to the barrier.

For each thread that wants to talk to the multithreaded barrier, the thread must create a `Buffers` and send data in that. The `Buffers` external thread interface to multithreaded barrier is only safe if it is used in a 1 to 1 relationship.

# usage

To compile
```
gcc barrier-runtime.c -o barrier-runtime -O3 -luring 
```

To run
```
./barrier-runtime
```


# LICENCE

Copyright (C) 2023 by Samuel Michael Squire sam@samsquire.com                                                                                         

Permission to use, copy, modify, and/or distribute this software for any purpose with or without fee is hereby granted.                               

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.   
