
/*
Copyright (C) 2023 by Samuel Michael Squire sam@samsquire.com

Permission to use, copy, modify, and/or distribute this software for any purpose with or without fee is hereby granted.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

gcc disruptor.c -o disruptor -O3 -luring 
./disruptor

Samuel Michael Squire's disruptor
from https://github.com/samsquire/assembly

This disruptor C code is Zero Clause BSD licenced.
*/
#define _GNU_SOURCE
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
#include <math.h>
#include <sched.h>

#define READER 1
#define WRITER 0

#define TICKSECONDS 0
#define TICK 150000L

struct Snapshot {
  struct timespec start;
  struct timespec end;
  volatile int complete;
};

struct Thread {
  int thread_index;
  struct Thread *sender;
  struct Snapshot * data;
  volatile int start;
  volatile int end;
  volatile int mode;
  long size;
  volatile int running;
  cpu_set_t *cpu_set;
};

void * disruptor_thread(void * arg) {
  struct Thread *data = arg;
  printf("in disruptor thread %d i am a %d\n", data->thread_index, data->mode);
  if (data->mode == WRITER) {
    while (data->running == 1) {
      if ((data->end + 1) % data->size == data->start) {
        // printf("Full\n"); 
        // if (data->running == 2) { data->running = -1; }
      } else {
        // printf("Wrote\n");
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->data[data->end].start);
        data->data[data->end].complete = 0;
        // data->data[data->end] = item;
        data->end = (data->end + 1) % data->size;
        asm volatile ("mfence" ::: "memory");
      } 
    } 
  } 
  else if (data->mode == READER) {
    struct timespec rem2;
    struct timespec preempt = {
      TICKSECONDS,
      TICK };
    struct Thread *sender = data->sender;
    while (data->running == 1) {
      if (sender->end == sender->start) {
        asm volatile ("mfence" ::: "memory");
        // printf("Empty\n"); 
        // if (data->running == 2) { data->running = -1; }
        // nanosleep(&preempt , &rem2);
      } else {
        clock_gettime(CLOCK_MONOTONIC_RAW, &sender->data[sender->start].end);
        sender->data[sender->start].complete = 1;
        // printf("Read %d\n", data->thread_index);
        // free(data->sender->data[data->sender->start]);
        sender->start = (sender->start + 1) % data->size;
      }
      
    } 
  } 
  printf("Finished\n");
  return 0;
}

int main() {
  /**

   We want a topology that allows fast forks and callbacks.

  */   

  int thread_count = 12;
  long buffer_size = pow(2, 12);
  printf("Buffer size (power of 2) %ld\n", buffer_size);
  int groups = 1; /* thread_count / 2 */ 
  printf("Group count %d\n", groups);
  struct Thread *thread_data = calloc(groups * 2, sizeof(struct Thread)); 
  pthread_attr_t      *attr = calloc(groups * 2, sizeof(pthread_attr_t));
  pthread_t *thread = calloc(groups * 2, sizeof(pthread_t));


   /* Set affinity mask to include CPUs 0 to 7. */
  int cores = 6;
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 2; 
    int corestart = x * 3; 
    int coreend = corestart + 3; 
    int receiver = sender + 1; 
    printf("%d is linked to %d\n", receiver, sender);
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    CPU_ZERO(sendercpu);
    for (int j = 0 ; j < cores; j++) {
      printf("assigning sender %d to core %d\n", sender, j);
      CPU_SET(j, sendercpu);
    }
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    CPU_ZERO(receivercpu);
    for (int j = 0 ; j < cores ; j++) {
      printf("assigning receiver %d to core %d\n", receiver, j);
      CPU_SET(j, receivercpu);
    }
     
    thread_data[sender].thread_index = sender;
    thread_data[sender].cpu_set = sendercpu;
    thread_data[sender].mode = WRITER;
    thread_data[sender].running = 1;
    thread_data[sender].size = buffer_size;
    thread_data[sender].data = calloc(buffer_size, sizeof(struct Snapshot));
    printf("Created data for %d\n", sender);
    thread_data[receiver].thread_index = receiver;
    thread_data[receiver].cpu_set = receivercpu;
    thread_data[receiver].running = 1;
    thread_data[receiver].mode = READER;
    thread_data[receiver].size = buffer_size;
    thread_data[receiver].sender = &thread_data[sender];
    printf("Creating sender thread %d\n", sender);
    printf("Creating receiver thread %d\n", receiver);
    asm volatile ("mfence" ::: "memory");
  }
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 2; 
    int receiver = sender + 1; 
    
    pthread_create(&thread[receiver], &attr[receiver], &disruptor_thread, &thread_data[receiver]);
    int ret = pthread_attr_setschedpolicy(&attr[receiver], SCHED_RR);
    if (ret) {
            printf("pthread setschedpolicy failed\n");
            exit(1);
    }
    pthread_create(&thread[sender], &attr[sender], &disruptor_thread, &thread_data[sender]);
    ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_RR);
    if (ret) {
            printf("pthread setschedpolicy failed\n");
            exit(1);
    }
    printf("set scheduling\n");
    // pthread_setaffinity_np(thread[sender], sizeof(thread_data[sender].cpu_set), thread_data[sender].cpu_set);
    //pthread_setaffinity_np(thread[receiver], sizeof(thread_data[receiver].cpu_set), thread_data[receiver].cpu_set);
    struct timespec rem2;
    struct timespec preempt = {
      0,
      TICK };
    // printf("Waiting before starting next disruptor %ld ns\n", TICK);
    // nanosleep(&preempt , &rem2);
    }
  int seconds = 10;
  struct timespec rem2;
  struct timespec preempt = {
    seconds,
    0 };
  printf("Sleeping for %d seconds\n", seconds);
  nanosleep(&preempt , &rem2);
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 2; 
    int receiver = sender + 1; 
    thread_data[sender].running = 0;
    thread_data[receiver].running = 0;
  }
  for (int x = 0 ; x < groups ; x++) {
    void * res1;
    void * res2;
    int sender = x * 2; 
    int receiver = sender + 1; 
    pthread_join(thread[sender], res1);
    pthread_join(thread[receiver], res2);
  }
  
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 2; 
    int receiver = sender + 1;
    int incompletes = 0;
    printf("Inspecting sender %d\n", sender);
    printf("%d %d\n", thread_data[sender].start, thread_data[sender].end);
    for (int y = 0 ; y < buffer_size; y++) {
      if (thread_data[sender].data[y].complete == 1) {
        struct timespec start = thread_data[sender].data[y].start;
        struct timespec end = thread_data[sender].data[y].end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("rb %d Read %ld %ld\n", sender, seconds, seconds2);
      } else {
        incompletes++;
      }
    }
    printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
