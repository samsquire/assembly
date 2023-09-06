#include <ctype.h>
#include <errno.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static 
void *func(void *data) {
  printf("Hi from thread\n");
  return 0;
}

struct data {
  int data;
};

int main() {
  ssize_t             stack_size;
  pthread_attr_t      attr;
  pthread_t thread;
  struct data data; 

  int s = pthread_create(&thread, &attr,
                            &func, &data); 
  void *result;
  pthread_join(thread, &result);
}

