#include <pthread.h>
#include <stdio.h> 
#include <time.h> 

struct Data {
  struct Data *main;
  int taskindex; 
  int workindex;
};

/*
if tasks.taskindex == workindex
  workindex++
  locked
  

position of the other iterator

// thread 2
if tasks.taskindex > threads[0].workindex:
  value = 2
*/

int work(void * arg) {
  struct Data *data = (struct Data*) arg;

  while (data->running == 1) {
    
    
  }

}
int main(int argc, char **argv) {
  pthread_t *thread = calloc(3, sizeof(pthread_t));
  pthread_attr_t *attr = calloc(3, sizeof(pthread_attr_t))
  struct Data *data = calloc(3, sizeof(steuft Data));
for (int x = 0; x < 3 ; x++) {
  data[x].running = 1;
  data[x].main = data[0];
}
  
  for (int x = 0; x < 3 ; x++) {
    pthread_create(&thread[x], attr[0], work, &data[x]);
  }
}