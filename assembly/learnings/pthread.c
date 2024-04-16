#include <ctype.h>
#include <errno.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

void *func(void *data) {
  printf("Hi from thread\n");
  return 0;
}

struct data {
  int data;
};

int main() {
  ssize_t             stack_size;
  pthread_attr_t      attr;;
  pthread_attr_t      attr2 = {0};
  pthread_t thread = {0};
  pthread_t thread2 = {0};
  
  struct data data; 

   memset(&attr, 0, sizeof(pthread_attr_t));
  printf("atrr %d %d\n", sizeof(pthread_t), sizeof(pthread_attr_t));
  int s = pthread_create(&thread, &attr,

                            func, &data); 
  printf("thread 1 created %ld %ld\n", sizeof(pthread_t), sizeof(pthread_attr_t));
  
   int d = pthread_create(&thread2, &attr2,
                           func, &data); 
  printf("thread 2 created\n");
  void *result;
  pthread_join(thread, &result);
   pthread_join(thread2, &result);
}

