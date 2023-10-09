/*
Copyright (C) 2023 by Samuel Michael Squire sam@samsquire.com

Permission to use, copy, modify, and/or distribute this software for any purpose with or without fee is hereby granted.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.


Samuel Michael Squire's multithreaded barrier runtime

Includes Samuel Michael Squire's nonblocking barrier ported from
Java to C. This code is Zero Clause BSD licenced.

see https://github.com/samsquire/multiversion-concurrency-control
for Java version
NonBlockingBarrierSynchronizationPreempt.java

*/
#include <pthread.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <liburing.h>
#include <sys/time.h>
#define TIMER 0
#define WORKER 1
#define IO 2
#define EXTERNAL 3

#define DURATION 10
#define QUEUE_DEPTH             256

struct Buffers {
  int count; 
  struct Buffer *buffer;
};
struct Buffer {
  void * data; 
  volatile int available;
};

struct BarrierTask {
  int task_index;
  int rerunnable;
  volatile int arrived; 
  long n; 
  long v; 
  int (*run)(volatile struct BarrierTask*);
  int (*protected)(volatile struct BarrierTask*);
  struct KernelThread *thread;
  volatile int thread_index;
  int thread_count;
  volatile int available;
  int task_count;
  volatile int scheduled;
  struct Snapshot *snapshots;
  long snapshot_count;
  long current_snapshot;
};

struct KernelThread {
  int thread_index;
  int type; 
  int preempt_interval;
  struct KernelThread *threads;
  int thread_count;
  int total_thread_count;
  volatile struct BarrierTask *tasks;
  int task_count;
  volatile int running;
  struct ProtectedState *protected_state;
  struct Buffers *buffers;
};

struct ProtectedState {
  long protected;
  int modcount;
};

struct Snapshot {
  struct timeval start;
  struct timeval end;
};

void* io_thread(void *arg) {
  struct KernelThread *data = arg;
  struct io_uring ring;
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
  //while (data->running == 1) {
    
  //}
  printf("Finished io thread\n");
  return 0;
}

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

          // printf("In thread %d %d\n", data->thread_index, t);
          data->tasks[t].run(&data->threads[data->thread_index].tasks[t]);
          //if (t == data->thread_index) {
          //  data->tasks[t].protected(&data->threads[data->thread_index].tasks[t]);
          //}
          data->tasks[t].arrived++;
          asm volatile ("mfence" ::: "memory");
          // break;
        } else {
          // printf("%d %d %d\n", data->thread_index, t, arrived);
          break;
        }   
      } else {

           // printf("%d not available\n", t);
      }
    }
  } 
  return 0;
}

void* timer_thread(void *arg) {
  long tick = 1500000L;
  long tickseconds = 0;
  // long tick = 0L;
  long times = ((1000000000L*10L)/tick);
  // long times = tickseconds * 10;
  
  struct KernelThread *data = arg;
  printf("In timer task %d\n", data->thread_index);
  struct timespec rem;
  struct timespec rem2;
  struct timespec preempt = {
    tickseconds,
    tick };
  struct timespec req = {
    DURATION,
    0 };
  
  int y = 0;
  int n = 0;

  printf("Will sleep %ld times\n", times);
  while (data->running && n < times) {
    n++;
    nanosleep(&preempt , &rem2);
    // preempt tasks
    for (int x = 0 ; x < data->thread_count ; x++) {
        int next = (y + 1) % data->threads[x].task_count;
        data->threads[x].tasks[next].scheduled = 1;
        data->threads[x].tasks[y].scheduled = 0;
    }
    asm volatile ("mfence" ::: "memory");
    y++;
    if (y >= data->threads[0].task_count) {
      y = 0;
    }
  }
  printf("Finished\n");
  while (data->running) {
    // nanosleep(&req , &rem);
    for (int x = 0 ; x < data->total_thread_count ; x++) {
      data->threads[x].running = 0;
    }
    // forcefully deschedule all tasks
    for (int x = 0 ; x < data->thread_count ; x++) {
      for (int y = 0 ; y < data->task_count ; y++) {
        data->threads[x].tasks[y].scheduled = 0;
      }
    }
    asm volatile ("mfence" ::: "memory");
    printf("Slept \n");
    data->running = 0;
  }
  printf("Timer thread stopping\n");
  return 0;
}

void * external_thread(void *arg) {
  struct KernelThread *data = arg; 

  struct timespec req = {
    1,
    0 };
  struct timespec rem;

  while (data->running == 1) {
    nanosleep(&req , &rem);
    // printf("External thread wakeup...\n");
    for (int x = 0; x < data->buffers->count; x++) {
      //printf("Writing to buffer\n");
      if (data->buffers->buffer[x].available == 0) {
        data->buffers->buffer[x].data = "Hello world";
        data->buffers->buffer[x].available = 1;
      }
    }
    asm volatile ("mfence" ::: "memory");
  }
  return 0; 
}

int do_protected_write(volatile struct BarrierTask *data) {

  struct ProtectedState *protected = data->thread->protected_state;
  data->v++; // thread local
    // printf("Protected %d %d\n", data->task_index, data->thread_index);
  protected->protected++; // shared between all threads
  return 0; 
}

int barriered_work_ingest(volatile struct BarrierTask *data) {
  // printf("Ingest task\n");
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    // printf("Checking buffer %d\n", data->thread->buffers->buffer[x].available);
    if (data->thread->buffers->buffer[x].available == 1) {
      // printf("Ingested %s\n", (char*)data->thread->buffers->buffer[x].data);
      data->thread->buffers->buffer[x].available = 0;
      asm volatile ("mfence" ::: "memory");
    }
  }
}

int barriered_work(volatile struct BarrierTask *data) {
  // printf("In barrier work task %d %d\n", data->thread_index, data->task_index);
  // printf("%d Arrived at task %d\n", data->thread_index, data->task_index);
  volatile long *n = &data->n;
  if (data->thread_index == data->task_index) {
    gettimeofday(&data->snapshots[data->current_snapshot].start, NULL);
    int modcount = ++data->thread->protected_state->modcount;
    while (data->scheduled == 1) {
      data->n++;
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
    }
    if (modcount != data->thread->protected_state->modcount) {
      printf("Race condition!\n");
    }
    gettimeofday(&data->snapshots[data->current_snapshot].end, NULL);
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
  } else {
      while (data->scheduled == 1) {
        data->n++;
      }
  }
  return 0;
}


int barriered_nulltask(volatile struct BarrierTask *data) {
  // printf("In barrier null task %d %d\n", data->thread_index, data->task_index);
  return 0;
}
int barriered_steal(volatile struct BarrierTask *data) {
  // printf("In barrier steal task %d %d\n", data->thread_index, data->task_index);
  return 0;
}
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

int after(struct timeval left, struct timeval right) {
  return left.tv_sec > right.tv_sec &&
         left.tv_usec > right.tv_usec;
}

int within(struct timeval a, struct timeval b, struct timeval c, struct timeval d) {
  if (a.tv_sec <- b.tv_sec && a.tv_usec <= b.tv_usec &&
   c.tv_sec <= d.tv_sec && c.tv_usec <= d.tv_usec) {
    return 1;
  }
  return 0;
}

int overlap(struct Snapshot left, struct Snapshot right) {

  if (after(left.start, right.start) && after(right.end, left.end)) {
    return 1;
  }
  if (after(right.start, left.start) && after(left.end, right.end)) {
    return 1;
  }
  if (within(left.start, right.start, right.end, left.end) == 1) {
    return 1;
  }
  if (within(right.start, left.start, left.end, right.end) == 1) {
    return 1;
  }
  return 0;
}

int verify(struct KernelThread *thread_data, int thread_count) {

  for (int x = 0 ; x < thread_count; x++) {
    for (int z = 0 ; z < thread_count; z++) {
      if (z != x)  {
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
          printf("Verifying thread %d\n", x);
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);

            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {

                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
                  /*
                     if (thread_data[x].tasks[y].snapshots[n].start.tv_sec <= thread_data[z].tasks[k].snapshots[m].start.tv_sec &&
                     thread_data[x].tasks[y].snapshots[n].start.tv_usec <= thread_data[z].tasks[k].snapshots[m].start.tv_usec &&
                     thread_data[z].tasks[k].snapshots[m].end.tv_sec >= thread_data[x].tasks[y].snapshots[n].end.tv_sec &&
                     thread_data[z].tasks[k].snapshots[m].end.tv_usec >= thread_data[x].tasks[y].snapshots[n].end.tv_usec) {
                   */

                  printf("Race condition %ld  %ld\n", thread_data[x].tasks[y].snapshots[n].start.tv_usec, thread_data[z].tasks[k].snapshots[m].start.tv_usec );
                }

                } 
              }

            }
          }
        }
      } 
    }


  return 0;
}

int main() {
  int thread_count = 10;
  int timer_count = 1;
  int io_threads = 1;
  int external_threads = 3;
  int buffer_size = 10;
  int total_threads = thread_count + timer_count + io_threads + external_threads;
  struct ProtectedState *protected_state = calloc(1, sizeof(struct ProtectedState));
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 

  int barrier_count = thread_count;
  int total_barrier_count = barrier_count + 1;
  int timer_index = thread_count;
  int io_index = timer_index + timer_count;

  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
  
  for (int x = 0 ; x < external_threads; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
    }
  }

  for (int x = 0 ; x < total_threads ; x++) {
    printf("Creating kernel thread %d\n", x);
    thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    thread_data[x].task_count = total_barrier_count;
    thread_data[x].protected_state = protected_state;

      struct BarrierTask *barriers = calloc(barrier_count + 1, sizeof(struct BarrierTask));
      thread_data[x].tasks = barriers;

      for (int y = 0 ; y < barrier_count ; y++) {
        if (x == y) {
            thread_data[x].tasks[y].protected = do_protected_write; 
        }
        thread_data[x].tasks[y].snapshot_count = 99999;
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
        thread_data[x].tasks[y].current_snapshot = 0;
        thread_data[x].tasks[y].thread_index = x;
        thread_data[x].tasks[y].thread = &thread_data[x]; 
        thread_data[x].tasks[y].available = 1;
        thread_data[x].tasks[y].arrived = 0;
        thread_data[x].tasks[y].thread_count = thread_count;
        thread_data[x].tasks[y].task_count = total_barrier_count;
        thread_data[x].tasks[y].task_index = y;
        if (y == barrier_count - 1) {
          if (x == thread_count - 1) {
            thread_data[x].tasks[y].run = barriered_steal; 
          } else {
            thread_data[x].tasks[y].run = barriered_nulltask; 
          }
        } else {
          if (x < external_threads) { 
            thread_data[x].buffers = buffers;
            thread_data[x].tasks[y].run = barriered_work_ingest; 
          } else {
            thread_data[x].tasks[y].run = barriered_work; 

          }
        }
      }
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = thread_count; 
      thread_data[x].tasks[barrier_count].thread_index = x; 
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].thread_index = x;
    thread_data[x].task_count = total_barrier_count;
  }
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));

  thread_data[thread_count].type = TIMER;
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  thread_data[thread_count].threads = thread_data;
  thread_data[thread_count].thread_count = thread_count;
  thread_data[thread_count].thread_index = 0;

  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
  for (int x = 0 ; x < thread_count ; x++) {
    thread_data[x].type = WORKER;
    thread_data[x].running = 1;
    pthread_create(&thread[x], &timer_attr[x], &barriered_thread, &thread_data[x]);
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    printf("Creating IO thread\n");
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  for (int x = io_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];

    thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    void * result; 
    pthread_join(thread[x], &result);
    printf("Finished thread %d\n", x);
  }
  long total = 0;
  long v = 0;
  for (int x = 0 ; x < thread_count ; x++) {

    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
      total += thread_data[x].tasks[n].n;
      v += thread_data[x].tasks[n].v;
    }
  }
  printf("Total Requests %ld\n", total);
  printf("Total Protected %ld\n", protected_state->protected);
  printf("Total V %ld\n", v);
  printf("Total Requests per second %ld\n", total / DURATION);
  // verify(thread_data, thread_count);
  return 0;

}
