#include <pthread.h>
#include <stdlib.h>
#include <stdio.h>

#define TIMER 0
#define WORKER 1

struct BarrierTask {
  int index;
  int rerunnable;
  volatile int arrived; 
  long n; 
  int (*run)(struct BarrierTask*);
  struct KernelThread *thread;
};

struct KernelThread {
  int index;
  int type; 
  int preempt_interval;
  struct KernelThread *threads;
  int thread_count;
  struct BarrierTask *tasks;
  int task_count;
};


void* barriered_thread(void *arg) {
  struct KernelThread *data = arg;
  printf("In barrier task %d", data->index);
  return 0;
}
int barriered_work(struct BarrierTask *data) {
  printf("In barrier steal task %d", data->index);
  return 0;
}
int barriered_steal(struct BarrierTask *data) {
  printf("In barrier steal task %d", data->index);
  return 0;
}
int barriered_reset(struct BarrierTask *data) {
  printf("In barrier reset task %d", data->index);
  return 0;
}

int main() {
  int thread_count = 12;
  int timer_count = 1;
  struct KernelThread *thread_data = calloc(thread_count + timer_count, sizeof(struct KernelThread)); 

  for (int x = 0 ; x < thread_count ; x++) {
    printf("Creating kernel thread %d\n", x);
    thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    for (int n = 0 ; n < thread_count ; n++) {
      int barrier_count = thread_count;
      thread_data[x].task_count = barrier_count;
      struct BarrierTask *barriers = calloc(barrier_count + 1, sizeof(struct BarrierTask));
      thread_data[x].tasks = barriers;

      for (int y = 0 ; y < barrier_count ; y++) {
        if (y == barrier_count - 1) {
          thread_data[x].tasks[y + 1].run = barriered_steal; 
        } else {
          thread_data[x].tasks[y].run = barriered_work; 
        }
      }
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
    }
  }

  pthread_attr_t      *timer_attr = calloc(thread_count + timer_count, sizeof(pthread_attr_t));
  pthread_t *thread = calloc(thread_count + 1, sizeof(pthread_t));

  thread_data[0].type = TIMER;

  pthread_create(&thread[0], &timer_attr[0], &barriered_thread, &thread_data[0]);
  for (int x = 1 ; x < thread_count ; x++) {
    thread_data[0].type = WORKER;
    pthread_create(&thread[x], &timer_attr[x], &barriered_thread, &thread_data[x]);
  }

  
  return 0;

}
