
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

#define READER 0
#define WRITER 1

struct Snapshot {
  struct timespec start;
  struct timespec end;
};

struct Thread {
  int thread_index;
  struct Thread *sender;
  struct Snapshot * data;
  volatile int start;
  volatile int end;
  int mode;
  long size;
  volatile int running;
};

void * disruptor_thread(void * arg) {
  struct Thread *data = arg;
  if (data->mode == WRITER) {
    while (data->running) {
      int next = (data->end + 1);
      if (next % data->size == data->start) {
        //printf("Full\n"); 
      } else {
        // printf("Wrote\n");
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->data[data->end].start);
        // data->data[data->end] = item;
        data->end = next % data->size;
        asm volatile ("mfence" ::: "memory");
      } 
    } 
  } 
  if (data->mode == READER) {
    struct Thread *sender = data->sender;
    while (data->running == 1) {
      if (sender->end == sender->start) {
        // printf("Empty\n"); 
      } else {
        clock_gettime(CLOCK_MONOTONIC_RAW, &sender->data[data->sender->start].end);
        // free(data->sender->data[data->sender->start]);
        
        sender->start = (sender->start + 1) % sender->size;
        asm volatile ("mfence" ::: "memory");
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
  long buffer_size = 2L << 28;
  printf("Buffer size (power of 2) %ld\n", buffer_size);
  int groups = 1; 
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
  // groups = 6
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 2; 
    int receiver = sender + 1; 
    thread_data[sender].thread_index = sender;
    thread_data[sender].mode = WRITER;
    thread_data[sender].running = 1;
    thread_data[sender].size = buffer_size;
    thread_data[sender].data = calloc(buffer_size, sizeof(struct Snapshot));
    thread_data[receiver].thread_index = receiver;
    thread_data[receiver].running = 1;
    thread_data[receiver].mode = READER;
    thread_data[receiver].size = buffer_size;
    thread_data[receiver].sender = &thread_data[sender];
    printf("Creating sender thread %d\n", sender);
    printf("Creating receiver thread %d\n", receiver);
  }
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 2; 
    int receiver = sender + 1; 
    pthread_create(&thread[sender], &attr[sender], &disruptor_thread, &thread_data[sender]);
    pthread_create(&thread[receiver], &attr[receiver], &disruptor_thread, &thread_data[receiver]);
    }
  int seconds = 5;
  printf("Sleeping for %d seconds\n", seconds);
  sleep(seconds);
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 2; 
    int receiver = sender + 1; 
    thread_data[sender].running = 0;
    thread_data[receiver].running = 0;
    void * res1;
    void * res2;
    pthread_join(thread[sender], res1);
    pthread_join(thread[receiver], res2);
  }
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 2; 
    int receiver = sender + 1;
    for (int y = 0 ; y < thread_data[sender].end ; y++) {
    struct timespec start = thread_data[sender].data[y].start;
    struct timespec end = thread_data[sender].data[y].end;
    const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    printf("Read %ld %ld\n", seconds, seconds2);
    }
  }

  return 0;
}
