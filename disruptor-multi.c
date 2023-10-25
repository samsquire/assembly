
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
  struct timespec *end;
  volatile int *complete;
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
  struct Thread **readers;
  int readers_count;
  int reader_index;
};

void * disruptor_thread(void * arg) {
  struct Thread *data = arg;
  printf("in disruptor thread %d i am a %d\n", data->thread_index, data->mode);
  if (data->mode == WRITER) {
    int anyfull = 0;
    while (data->running == 1) {
      asm volatile ("mfence" ::: "memory");
      anyfull = 0;
      int next = (data->end + 1) % data->size;
      for (int x  = 0 ; x < data->readers_count; x++) {
        if (next == data->readers[x]->start) {
          anyfull = 1;
          // printf("waiting for %d\n", x);
          break;
          // if (data->running == 2) { data->running = -1; }
        } else {
        } 
      }

      if (anyfull == 0) {
        // printf("Wrote\n");
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->data[data->end].start);
        for (int n = 0 ; n < data->readers_count ; n++) { 
          data->data[data->end].complete[n] = 0;
        }
        // data->data[data->end] = item;
        data->end = (data->end + 1) % data->size;
      } else {
        continue;
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
      asm volatile ("mfence" ::: "memory");
      // asm volatile ("sfence" ::: "memory");
      if (sender->end == data->start) {
        // printf("Empty\n"); 
        // if (data->running == 2) { data->running = -1; }
        // nanosleep(&preempt , &rem2);
      } else {
        clock_gettime(CLOCK_MONOTONIC_RAW, &sender->data[data->start].end[data->reader_index]);
        sender->data[data->start].complete[data->reader_index] = 1;
        // printf("Read %d\n", data->thread_index);
        // free(data->sender->data[data->sender->start]);
        data->start = (data->start + 1) % data->size;
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

  long buffer_size = pow(2, 12);
  printf("Buffer size (power of 2) %ld\n", buffer_size);
  int groups = 3; /* thread_count / 2 */ 
  printf("Group count %d\n", groups);
  int readers_count = 2;
  printf("Readers count %d\n", readers_count);
  int thread_count = groups * (readers_count + 1);
  printf("Total thread count %d\n", thread_count);
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));

  int ret = setpriority(PRIO_PROCESS, 0, -20);
  if (ret) {
    perror("priority set"); 
    exit(1);
  }

   /* Set affinity mask to include CPUs 0 to 7. */
  int cores = 12;
  // 0, 3, 6
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 3; 
    int receiver = sender + 1; 
    int receiver2 = receiver + 1; 
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    CPU_ZERO(sendercpu);
    for (int j = 0 ; j < cores; j++) {
      // printf("assigning sender %d to core %d\n", sender, j);
      CPU_SET(j, sendercpu);
    }
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    CPU_ZERO(receivercpu);
    for (int j = 0 ; j < cores ; j++) {
      // printf("assigning receiver %d to core %d\n", receiver, j);
      CPU_SET(j, receivercpu);
    }
     
    thread_data[sender].thread_index = sender;
    thread_data[sender].cpu_set = sendercpu;
    thread_data[sender].mode = WRITER;
    thread_data[sender].running = 1;
    thread_data[sender].size = buffer_size;
    thread_data[sender].readers = calloc(readers_count, sizeof(struct Thread*));
    thread_data[sender].data = calloc(buffer_size, sizeof(struct Snapshot));
    for (int n = 0 ; n < buffer_size ; n++) {
      thread_data[sender].data[n].end = calloc(readers_count, sizeof(struct timespec));
      thread_data[sender].data[n].complete = calloc(readers_count, sizeof(int));
    }
    thread_data[sender].readers_count = readers_count;
    // printf("Created data for %d\n", sender);
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
      thread_data[j].thread_index = j;
      thread_data[j].reader_index = receiver_index;
      thread_data[j].cpu_set = receivercpu;
      thread_data[j].running = 1;
      thread_data[j].mode = READER;
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
      thread_data[sender].readers[receiver_index] = &thread_data[j];
      printf("Setting up receiver thread %d %d\n", j, receiver_index);
    }
    printf("Creating sender thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 3; 
    int receiver = sender + 1; 
    
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
      printf("Creating receiver thread %d\n", j);
      
      int ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
      if (ret) {
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      ret = pthread_attr_setschedparam(&attr[j], &param);
      if (ret) {
              printf("pthread setschedparam failed\n");
              exit(1);
      }
      
      pthread_create(&thread[j], &attr[j], &disruptor_thread, &thread_data[j]);
      pthread_setaffinity_np(thread[j], sizeof(thread_data[receiver].cpu_set), thread_data[receiver].cpu_set);
    }
      
      int ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
      if (ret) {
               printf("pthread setschedpolicy failed\n");
               exit(1);
      }
      param2.sched_priority = 0;
      ret = pthread_attr_setschedparam(&attr[sender], &param2);
      if (ret) {
              printf("pthread setschedparam failed\n");
              exit(1);
      }
    pthread_create(&thread[sender], &attr[sender], &disruptor_thread, &thread_data[sender]);
    pthread_setaffinity_np(thread[sender], sizeof(thread_data[sender].cpu_set), thread_data[sender].cpu_set);
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
    int sender = x * 3; 
    int receiver = sender + 1; 
    thread_data[sender].running = 0;
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
      thread_data[j].running = 0;
    }
  }
  for (int x = 0 ; x < groups ; x++) {
    void * res1;
    void * res2;
    int sender = x * 3; 
    int receiver = sender + 1; 
    pthread_join(thread[sender], res1);
    for (int j = receiver, receiver_index = 0; j < sender + readers_count + 1; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    }
  }
  
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 3; 
    int receiver = sender + 1;
    int incompletes = 0;
    printf("Inspecting sender %d\n", sender);
    for (int y = 0 ; y < buffer_size; y++) {
      int compcount = 0;
      for (int n = 0 ; n < readers_count ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
          compcount++;
        }
      }
      if (compcount == readers_count) {
        for (int n = 0 ; n < readers_count ; n++) {
          if (thread_data[sender].data[y].complete[n] == 1) {
            // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
            struct timespec start = thread_data[sender].data[y].start;
            struct timespec end = thread_data[sender].data[y].end[n];
            const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
            const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
            printf("rb %d %d Read %ld %ld\n", sender, n, seconds, seconds2);
          } else {
            incompletes++;
          }
        }
      }
    }
    printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
