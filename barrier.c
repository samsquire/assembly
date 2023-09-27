/*
Copyright (C) 2023 by Samuel Michael Squire sam@samsquire.com

Permission to use, copy, modify, and/or distribute this software for any purpose with or without fee is hereby granted.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.


Samuel Michael Squire's nonblocking barrier ported from
Java to C

see https://github.com/samsquire/multiversion-concurrency-control
for Java version
NonBlockingBarrierSynchronizationPreempt.java

*/
#include <pthread.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#define TIMER 0
#define WORKER 1

#define DURATION 10

struct BarrierTask {
  int task_index;
  int rerunnable;
  volatile int arrived; 
  long n; 
  int (*run)(volatile struct BarrierTask*);
  struct KernelThread *thread;
  int thread_index;
  int thread_count;
  volatile int available;
  int task_count;
};

struct KernelThread {
  int thread_index;
  int type; 
  int preempt_interval;
  struct KernelThread *threads;
  int thread_count;
  volatile struct BarrierTask *tasks;
  int task_count;
  volatile int running;
};


void* barriered_thread(void *arg) {
  struct KernelThread *data = arg;
  // printf("In barrier task %d\n", data->thread_index);
  int t = 0;
  while (data->running == 1) {
    if (t >= data->task_count - 1) {
      t = 0;
    }
    for (; t < data->task_count; t++) {
      // printf("%d\n", t);
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
          asm volatile("" ::: "memory");
          //printf("%d Arrived at task %d\n", data->thread_index, t);
          break;
        } else {
          // printf("%d %d\n", t, arrived);
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
  struct KernelThread *data = arg;
  printf("In timer task %d\n", data->thread_index);
  struct timespec rem;
  struct timespec req = {
    DURATION,
    0 };
  while (data->running) {
    nanosleep(&req , &rem);
    for (int x = 0 ; x < data->thread_count ; x++) {
      data->threads[x].running = 0;
    }
    asm volatile("" ::: "memory");
    printf("Slept \n");
    data->running = 0;
  }
  printf("Timer thread stopping\n");
  return 0;
}
int barriered_work(volatile struct BarrierTask *data) {
  // printf("In barrier work task %d %d\n", data->thread_index, data->task_index);
  data->n++;
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
    // printf("Resetting %d\n", x);
    data->thread->tasks[x].arrived++; 
    data->thread->tasks[x].available = 1; 
  }
  asm volatile("" ::: "memory");
  return 0;
}

int main() {
  int thread_count = 11;
  int timer_count = 1;
  struct KernelThread *thread_data = calloc(thread_count + 1, sizeof(struct KernelThread)); 

  int barrier_count = thread_count;
  int total_barrier_count = barrier_count + 1;
  for (int x = 0 ; x < thread_count ; x++) {
    printf("Creating kernel thread %d\n", x);
    thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].thread_index = x;
    thread_data[x].task_count = total_barrier_count;

      struct BarrierTask *barriers = calloc(barrier_count + 1, sizeof(struct BarrierTask));
      thread_data[x].tasks = barriers;

      for (int y = 0 ; y < barrier_count ; y++) {
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
          thread_data[x].tasks[y].run = barriered_work; 
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

  pthread_attr_t      *timer_attr = calloc(thread_count + timer_count, sizeof(pthread_attr_t));
  pthread_t *thread = calloc(thread_count + 1, sizeof(pthread_t));

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

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < thread_count + timer_count ; x++) {
    void * result; 
    pthread_join(thread[x], &result);
    printf("Finished thread %d\n", x);
  }
  long total = 0;
  for (int x = 0 ; x < thread_count ; x++) {

    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
      total += thread_data[x].tasks[n].n;
    }
  }
  printf("Total Requests %ld\n", total);
  printf("Total Requests per second %ld\n", total / DURATION);
  return 0;

}
