#include <pthread.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>

#define DURATION 10

struct ThreadData {
  long n;
  int running;
};

void * benchmark_thread(void * arg) {
  struct ThreadData * data = arg;
  long n = 0;
  while (data->running == 1) {
    n++;
  }
  data->n = n;
  return 0;
}

int main(int argc, char argv[]) {

  int thread_count = 12; 
  int total_threads = thread_count;
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
  struct ThreadData *thread_data = calloc(thread_count, sizeof(struct ThreadData));
  printf("Starting benchmark\n");
  for (int x = 0 ; x < thread_count ; x++) {
    thread_data[x].running = 1;
  } 
  for (int x = 0 ; x < thread_count ; x++) {
    pthread_create(&thread[x], &timer_attr[x], &benchmark_thread, &thread_data[x]);
    printf("Created kernel thread %d\n", x);
  }

  struct timespec rem;
  struct timespec req = {
    DURATION,
    0 };
  nanosleep(&req , &rem);
  for (int x = 0 ; x < thread_count ; x++) {
    thread_data[x].running = 0;
  }
  asm volatile ("mfence" ::: "memory");
  long total = 0;
  for (int x = 0 ; x < thread_count ; x++) {
    total += thread_data[x].n; 
  }
  printf("Finished benchmark\n");
  printf("Requests %ld\n", total);
  printf("Requests per second %ld\n", total / DURATION);

  return 0;
}
