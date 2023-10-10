# multithreaded nonblocking barrier-runtime

This is my (Samuel Michael Squire, sam@samsquire.com) lock free algorithm and runtime for a nonblocking multithreaded barrier. It is Zero Clause BSD Licenced.

```
Total Requests 12243924844
Total Protected 382789962
Total V 382789962
Total Protected per second 38278996
Total money 0 (correct if 0 or 500)
Total external thread ingests per second 21585790
Total intra thread sends per second 776758223
Total Requests per second 1224392484
```

With 12 threads for 30 seconds, 12 threads all incrementing a long can do all the following: 1.2 billion additions, 776 million interthread sends, 21 million external thread ingests and 38 million critical section executions a second.

This algorithm is inspired by [Bulk synchronous parallel](https://en.wikipedia.org/wiki/Bulk_Synchronous_Parallel).

This algorithm uses ideas from my **M:N** thread scheduler, which is at [samsquire/preemptible-thread](https://github.com/samsquire/preemptible-thread).

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

In Go, if you are sending 64 bits of data to a channel, this causes unnecessary context switches in the go scheduler.

The data races reported by Thread Sanitizer do not affect correctness but allow this algorithm to be extremely performant this is because there is a **happens before** relationship between **arrived** and writes to arrived always come from the same thread.



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
  // we are synchronized
  char message[200];
  memset(&message, '\0', 200);

  sprintf(message, "Sending message from thread %d task %d", data->thread_index, data->task_index);
  if (data->thread_index == data->task_index) {

      void * tmp; 
      int next_task = (data->task_index + 1) % data->task_count;
      // swap this thread's write buffer with the next task
      for (int y = data->thread_count ; y > 0 ; y--) {
        tmp = data->thread->threads[y].tasks[data->task_index].mailboxes->lower; 
        data->thread->threads[y].tasks[data->task_index].mailboxes->lower = data->thread->threads[y].tasks[data->task_index].mailboxes->higher;
        // printf("move this this task task_index %d higher to %d lower\n", data->task_index, data->task_index);
        data->thread->threads[y].tasks[data->task_index].mailboxes->higher = data->thread->threads[y].tasks[next_task].mailboxes->higher;
        //printf("move next %d higher to %d higher\n", next_task, data->task_index);
        data->thread->threads[y].tasks[next_task].mailboxes->lower = tmp;
        // printf("move my %d lower to next %d lower\n",data->task_index, next_task);
      }

    struct Data *me = data->mailboxes->lower;
    for (int x = 0 ; x < me->messages_count ; x++) {
      data->sends++;
      // printf("%s\n", me->messages[x]);
    }
    me->messages_count = 0;

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
      while (data->scheduled == 1) {
        data->n++;
        struct Data *me = data->mailboxes->lower;
        if (me->messages_count < me->messages_limit) {

          me->messages[me->messages_count++] = message;
        } else {
          // printf("Starve!\n");
        }
      }
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

# LICENCE

Copyright (C) 2023 by Samuel Michael Squire sam@samsquire.com                                                                                         

Permission to use, copy, modify, and/or distribute this software for any purpose with or without fee is hereby granted.                               

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.   
