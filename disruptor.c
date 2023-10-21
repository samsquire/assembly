
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

struct Thread {
  int thread_index;

};

void * disruptor_thread(void * arg) {
  struct Thread *thread = arg;
  
  return 0;
}

int main() {
  /**

   We want a topology that allows fast forks and callbacks.

  */   
  int thread_count = 12;
  int groups = thread_count / 2; 
  struct Thread *thread_data = calloc(thread_count, sizeof(struct Thread)); 
  pthread_attr_t      *attr = calloc(thread_count, sizeof(pthread_attr_t));
  pthread_t *thread = calloc(thread_count, sizeof(pthread_t));
  // groups = 6
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 2; 
    int receiver = sender + 1; 
    thread_data[sender].thread_index = sender;
    thread_data[receiver].thread_index = receiver;
    printf("Creating sender thread %d\n", sender);
    printf("Creating receiver thread %d\n", receiver);
  }
  for (int x = 0 ; x < groups ; x++) {
    int sender = x * 2; 
    int receiver = sender + 1; 
    pthread_create(&thread[sender], &attr[thread_count], &disruptor_thread, &thread_data[sender]);
    pthread_create(&thread[receiver], &attr[thread_count], &disruptor_thread, &thread_data[receiver]);
    }

  return 0;
}
