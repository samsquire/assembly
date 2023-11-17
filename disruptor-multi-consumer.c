
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
  struct timespec start __attribute__((aligned (128)));
  struct timespec end __attribute__((aligned (128)));
  int *complete __attribute__((aligned (128)));
};

struct Thread {
  int thread_index;
  struct Thread *sender;
  struct Thread *reader;
  struct Snapshot * data;
  int start __attribute__((aligned (128)));
  int end __attribute__((aligned (128)));
  volatile int mode;
  long size;
  volatile int running;
  cpu_set_t *cpu_set;
  struct Thread **readers __attribute__((aligned (128)));
  int other_count;
  int reader_index;
  int multiple;
};

int min(long a, long b) {
  if (a < b) return a;
  if (b < a) return b;
  return a;
}

void * disruptor_thread(void * arg) {
  struct Thread *data = arg;
  printf("in disruptor thread %d i am a %d\n", data->thread_index, data->mode);
  int mina = data->size;
  
  int next = (data->end + 1) % data->size;
  if (data->mode == WRITER) {
    printf("I am writer\n");
    struct Thread *me = data->sender;
    next = (me->end + 1) % data->size;
    int anyfull = 0;
    while (data->running == 1) {
      asm volatile ("sfence" ::: "memory");
        // mina = min(mina, data->readers[x]->start);
        if ((data->end + 1) % me->size == me->start) {
          // printf("waiting for %d == %d\n", next, data->start);
          // if (data->running == 2) { data->running = -1; }
        } else {
         

          //for (int x = 0 ; x < data->size ; x++) {
            // printf("%d %d\n", next, mina);
            /*
            if (next == mina) {
              break;
            }*/
            // data->data[data->end] = item;
            int changed = me->end;
            while (!__sync_bool_compare_and_swap(&me->end, changed, (changed + 1) % me->size)) {
              changed = me->end;
            }
            // printf("%d Wrote %d\n", data->thread_index, me->end);
            clock_gettime(CLOCK_MONOTONIC_RAW, &me->data[changed].start);
            me->data[changed].complete[1] = 1;
            // asm volatile ("sfence" ::: "memory");
            /*if (next == mina) { break; } */
          }        
      } 
       
  } else if (data->mode == READER) {
    printf("I am reader\n");
    struct timespec rem2;
    struct timespec preempt = {
      0,
      TICK };
    struct Thread *sender = data->sender;
    struct Snapshot * rdata = sender->data;
    int cachedEnd = sender->end;
    int size = data->size;
    int index = data->reader_index;
    int me = 0;
    while (data->running == 1) {
      // printf("reading %d\n", data->thread_index); 
      // asm volatile ("sfence" ::: "memory");
      if (sender->end == sender->start) {
        // printf("Empty %d %d %d %d\n", sender->end, data->start, data->thread_index, data->reader_index); 
        // if (data->running == 2) { data->running = -1; }
        // nanosleep(&preempt , &rem2);
      } else {
        //for (int x = data->start; x < sender->end ; x++) {
          int changed = sender->start;
          // printf("%d %d\n", data->multiple, sender->start % data->multiple);
          if (data->start % data->other_count == data->multiple) {
            if (__sync_bool_compare_and_swap(&sender->start, changed, (changed + 1) % sender->size)) {
              // printf("Read %d,%d %d\n", data->thread_index, data->reader_index, sender->start);
              clock_gettime(CLOCK_MONOTONIC_RAW, &rdata[changed].end);
              rdata[changed].complete[0] = 1;
              cachedEnd = sender->end;
              // printf("next is %d\n", me);
              // asm volatile ("sfence" ::: "memory");
            } else {
              // printf("failed\n");
              // asm volatile ("sfence" ::: "memory");
              // cachedEnd = sender->end;
            }
          }
        //}
        // printf("Read %d\n", data->thread_index);
        // free(data->sender->data[data->sender->start]);
      }
      
    } 
  } 
  printf("Finished %d\n", data->mode);
  return 0;
}

int main() {
  /**

   We want a topology that allows fast forks and callbacks.

  */   

  int power = 20;
  long buffer_size = pow(2, power);
  printf("Buffer size (power of 2^%d) %ld\n", power, buffer_size);
  int groups = 1; /* thread_count / 2 */ 
  printf("Group count %d\n", groups);
  int writers_count = 1;
  int other_count = 2;
  int group_size = writers_count + other_count;
  printf("Readers count %d\n", other_count);
  int thread_count = groups * (other_count + writers_count);
  printf("Total thread count %d\n", thread_count);
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));

   /* Set affinity mask to include CPUs 0 to 7. */
  int cores = 12;
  int curcpu = 0;
  // 0, 3, 6
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + 1; 
    int receiver2 = receiver + 1; 
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    CPU_ZERO(sendercpu);
    for (int j = 0 ; j < cores ; j++) {
      // printf("assigning sender %d to core %d\n", sender, j);
      CPU_SET(j, sendercpu);
    }
    cpu_set_t *receivercpu = calloc(1, sizeof(cpu_set_t));
    CPU_ZERO(receivercpu);
    for (int j = 0; j < cores ; j++) {
      // printf("assigning receiver %d to core %d\n", receiver, j);
      CPU_SET(j, receivercpu);
    }
     
    thread_data[sender].thread_index = sender;
    thread_data[sender].cpu_set = sendercpu;
    thread_data[sender].mode = WRITER;
    thread_data[sender].running = 1;
    thread_data[sender].size = buffer_size;
    thread_data[sender].end = 0;
    thread_data[sender].sender = &thread_data[sender];
    thread_data[sender].readers = calloc(other_count, sizeof(struct Thread*));
    thread_data[sender].data = calloc(buffer_size, sizeof(struct Snapshot));
    for (int n = 0 ; n < buffer_size ; n++) {
      thread_data[sender].data[n].complete = calloc(other_count, sizeof(int));
    }
    thread_data[sender].other_count = other_count;
    // printf("Created data for %d\n", sender);
    int seq[] = {1, 2, 5};
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
      thread_data[j].thread_index = j;
      thread_data[j].reader_index = receiver_index;
      thread_data[j].multiple = receiver_index % other_count;
      thread_data[j].other_count = other_count;
     
      thread_data[j].cpu_set = receivercpu;
      thread_data[j].running = 1;
      thread_data[j].mode = READER;
      if (j == receiver) {
        thread_data[j].data = calloc(buffer_size, sizeof(struct Snapshot));
        for (int n = 0 ; n < buffer_size ; n++) {
          thread_data[j].data[n].complete = calloc(other_count, sizeof(int));
        }
      }
      thread_data[j].size = buffer_size;
      thread_data[j].sender = &thread_data[sender];
      thread_data[j].start = 0;
      thread_data[j].reader = &thread_data[sender];
      thread_data[j].readers = thread_data[sender].readers;
      thread_data[sender].readers[receiver_index] = &thread_data[j];
      printf("Setting up sender thread %d %d to sender %d\n", j, receiver_index, sender);
    }
    printf("Creating receiver thread %d\n", sender);
    asm volatile ("mfence" ::: "memory");
  }

  struct sched_param param2;
  struct sched_param param;
  param.sched_priority = 0;
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + 1; 
    
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
      printf("Creating receiver thread %d\n", j);
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[j], SCHED_OTHER);
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
      
      int ret;
      
      ret = pthread_attr_setschedpolicy(&attr[sender], SCHED_OTHER);
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
    int sender = x * group_size; 
    int receiver = sender + 1; 
    thread_data[sender].running = 0;
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
      thread_data[j].running = 0;
    }
  }
  for (int x = 0 ; x < groups ; x++) {
    void * res1;
    void * res2;
    int sender = x * group_size; 
    int receiver = sender + 1; 
    pthread_join(thread[sender], res1);
    for (int j = receiver, receiver_index = 0; j < sender + other_count + 1; j++, receiver_index++) {
      pthread_join(thread[j], res2);
    }
  }
  
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * group_size; 
    int receiver = sender + 1;
    int incompletes = 0;
    printf("Inspecting sender %d\n", receiver);
    for (int y = 0 ; y < buffer_size; y++) {
      int compcount = 0;
      for (int n = 0 ; n < 2 ; n++) {

        if (thread_data[sender].data[y].complete[n] == 1) {
          compcount++;
        }
      }
      // printf("%d\n", compcount);
      if (compcount == 2) {
          // printf("start and end %d %d\n", thread_data[sender + n].start, thread_data[sender].end);
          struct timespec start = thread_data[sender].data[y].start;
          struct timespec end = thread_data[sender].data[y].end;
          const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
          const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
          printf("rb %d Read %ld %ld\n", sender, seconds, seconds2);
      }
    }
    printf("Incompletes %d\n", incompletes);
  }

  return 0;
}
