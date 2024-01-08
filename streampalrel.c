#include <pthread.h>
#include <netinet/in.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <time.h>
#include <liburing.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <string.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/utsname.h>
#include <ctype.h>
#include <sys/eventfd.h>
#include <sched.h>

struct Log {
  int thread_index;
  int thread_count;
  struct Log **others;
  int * data;
  int data_size;
  long index;
  int running;
  long result;
  long mine;
};

void* stream(void * arg) {
  struct Log * log = arg;
  printf("log stream %d started\n", log->thread_index);
  while (log->running) {
    long start = 0;
    for (int x  = 0 ; x < log->thread_count ; x++) {
      start += log->others[x]->data[log->others[x]->index % log->data_size];
    }
    for (int x = 0 ; x < log->data_size; x++) {
      log->data[(log->index + 1) % log->data_size] = log->data[log->index % log->data_size] + 1;    
      log->result = start + log->data[log->index % log->data_size];
      log->index++;
      log->mine++;
    }
  }
  
  return (void*)log->result;
}

int main() {
  int thread_count = 12; 
  int total_threads = thread_count;
  int data_size = 1000000;

  struct Log * logs = calloc(thread_count, sizeof(struct Log));
  struct Log ** logptrs = calloc(thread_count, sizeof(struct Log*));
  for (int x = 0 ; x < thread_count ; x++) {
    logs[x].running = 1;
    logs[x].thread_index = x;
    logs[x].data_size = data_size;
    logs[x].thread_count = thread_count;
    logs[x].data = calloc(data_size, sizeof(int));
    logs[x].data[0] = 1;
    logs[x].mine = 1;
    logs[x].others = logptrs;
    logptrs[x] = &logs[x];
  }
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
  pthread_attr_t      *attr = calloc(total_threads, sizeof(pthread_attr_t));

  for (int x = 0 ; x < thread_count ; x++) {
    pthread_create(&thread[x], &attr[x], &stream, &logs[x]);
  }

  
  struct timespec rem2;
  struct timespec preempt = {
    5,
    0 };
  nanosleep(&preempt , &rem2);
  for (int x = 0 ; x < thread_count ; x++) {
    logs[x].running = 0;
  }
  asm volatile ("sfence":::"memory");

  for (int x = 0 ; x < thread_count ; x++) {
    void * result; 
    pthread_join(thread[x], &result);
  }
  long mine = 0;
  for (int x = 0 ; x < thread_count ; x++) {
    long start = 0;
    for (int y  = 0 ; y < logs[x].thread_count ; y++) {
      start += logs[x].others[y]->data[logs[x].others[y]->index % logs[x].data_size];
    }
    printf("start %ld result\n", start);
    mine += logs[x].mine;
  }
  printf("mine %ld result\n", mine);
}
