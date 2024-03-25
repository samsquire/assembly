#define _GNU_SOURCE
#include <err.h>
#include <errno.h>
#include <pthread.h>
#include <stdio.h> 
#include <time.h> 
#include <stdlib.h>
#include <string.h>
struct Work {
  int taskindex;
  int available __attribute__((aligned (128)));
};
// __attribute__((aligned (128)))
struct Data {
  struct Data *main;
  struct Data *threads;
  long freq ;
  int taskindex; 
  int workindex __attribute__((aligned (128)));
  int wantindex __attribute__((aligned (128)));
  int running;
  int worksize;
  int threadindex;
  int threadsize;
  struct Work *works;
  cpu_set_t *cpu_set;
  int failcounter;
  int loglevel;
  int *primes;
  int buckets;
  int availables;
  int bucketstart;
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

void * work(void * arg) {
  struct Data *data = (struct Data*) arg;
  char * output = calloc(100, sizeof(char));
  int found = 0;
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  int innerfind = 0;
  int bucketlim = ((data->threadindex + 1) * data->buckets) ;
  int bucketstart = data->bucketstart;
  printf("bucketlim %d\n", bucketlim);
  data->workindex = bucketstart;
  while (data->running == 1) {
    found = 0;
    innerfind = 0;
  //memset(output, 0, 100);
   
    //if (data->threadindex == 0 && data->main->workindex >= data->worksize) {
    /*if (data->main->workindex >= data->worksize){
        data->main->workindex = 0;
        printf("work epoch end\n");
        for (int x = 0 ; x < data->worksize; x++) {
          data->main->works[x].available = 1;
        }
   }*/
      asm volatile ("" ::: "memory");
      int allunavailable = 1;
      int available = 1;
      int target = 0;
    
    
    // printf("target: %d %d\n", target, bucketlim);
    int stride = 1;
    int end = 0;
    int start = 0;
    int mine = 1;
  
   for (int x = data->bucketstart ; x < bucketlim; x+= stride ) {
       //printf("%d\n", x); 
    if (data->main->works[x].available == 1 ) {
        target = x;
        found = 1;
        start = data->bucketstart;
        end = bucketlim;
     //printf("found\n");
      
      
        break;
    } else {
        
      
    }
   }
  data->workindex = target;
  {
    
  if (found == 0) {
    mine = 0;
  // printf("expired\n");
  
    
    
    currentbucket = (currentbucket + 1) % data->threadsize;
    if (currentbucket == data->threadindex) { currentbucket = (currentbucket + 1) % data->threadsize;}
    
    int stride = 1;
    
   for (int x = currentbucket * data->buckets ; x < (currentbucket * data->buckets) + data->buckets ; x+= stride ) {
        
    if (data->main->works[x].available == 1 ) {
        target = x;
      start = currentbucket * data->buckets;
      end = (currentbucket * data->buckets) + data->buckets- 1;
        innerfind = 1;
                break;
    } else {
        
      
    }
   }
  }
  
  
    
    
       //printf("syncing\n");
      data->threads[data->threadindex].wantindex = target;
      for (int x = 0; x < data->threadsize ; x++ ) {
        if (x == data->threadindex) {
          continue;
        }
        if (data->threads[x].wantindex != -1 && data->threads[x].wantindex == target
          ) {
       //printf("%d fail\n", data->threadindex);
          available = 0;
          data->threads[data->threadindex].wantindex = -1;
          
          break;
        }
      }
    if (found == 0) {
    //  printf("used up\n");
    }
  }
      if (available == 1 && data->main->works[target].available == 1) {
        if (innerfind == 1) {
         //printf("cb %d\n", data->threads[currentbucket].availables);
       data->threads[currentbucket].availables--;
        //  printf("stolen availablea\n");
        }
        if (found == 1) {
          //printf("availablesless\n");
          data->availables--;
        }
data->main->works[target].available = 0;
     //printf("work %d %d %d\n", start, end, data->workindex);
      
        //data->workindex = (data->threadindex * data->buckets);
        
        data->freq++;
        if (mine == 0) {
        //printf("[%d] stole %d from bucket %d\n", data->threadindex, target, currentbucket);
        }
        if (data->loglevel == 1) {
        if (data->threadindex == 0) {
          ;
        snprintf(output, 100, "queue owner [%d]: processing queue item %d", data->threadindex, target);
        printf("%s\n", output); 

        } else {
          
snprintf(output, 100, "queue other [%d]: stealing queue item %d", data->threadindex, target);
         printf("%s\n", output);
          
          
        } }
        
        data->threads[data->threadindex].wantindex = -1;
        //data->main->workindex = (target + 1);
        
          
        }
    
        
        //asm volatile ("sfence" ::: "memory");

        // data->main->workindex = (data->main->workindex+ 1) % data->worksize;
        
      
      

      
      // for (int x = 0 ; x < data->worksize; x++) {
        //asm volatile ("" ::: "memory");
      
          
          // data->main->works[x].taskindex = (data->main->works[x].taskindex + data->worksize - 1) % data->worksize;
      
  //
    if (data->threadindex == 0) {
  int availables = 0;
    
     for (int x = 0 ; x< data->threadsize ; x++) {
       availables += data->threads[x].availables;
     }
   // printf("%d availables\n", availables);
     if (availables == 0) {
       
          data->workindex = data->bucketstart;
                 {
      if (data->loglevel == 1) { printf("all used\n"); }
        
       // printf("xx %d %d\n", xx, bucketlim);
        for (int x = 0; x < data->threadsize ; x++) {
          data->threads[x].availables = data->buckets;
            data->threads[x].workindex = data->threads[x].bucketstart;


        }
      for (int x = 0; x < data->worksize; x++) {
        data->main->works[x].available = 1;
      }
      }
     }
      }}
}

int main(int argc, char **argv) {
  int debug = 0;
  int worksize = 30;
  srand(time(NULL));
  int primes[] = {3, 7, 13, 19, 23, 29, 31, 37};
  int threadsize = 3;
  int buckets = worksize / threadsize;
  printf("Starting %d workers\n", threadsize);
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  struct Work *works = calloc(worksize, sizeof(struct Work));
  
  for (int i = 0; i < worksize; i++) {
    works[i].taskindex = 2;
    works[i].available = 1;
    
  }
  int cpu = 0;
  data[0].works = works;
  for (int x = 0; x < threadsize ; x++) {
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
    CPU_SET(cpu += 1, data[x].cpu_set);
    printf("assigning thread %d to cpu %d\n", x, cpu);
    data[x].bucketstart = x * buckets ;
    data[x].loglevel = debug;
    data[x].running = 1;
    data[x].threadindex = x;
    data[x].worksize = worksize;
    data[x].availables = buckets;
    data[x].threadsize = threadsize;
    data[x].buckets = buckets;
    data[x].main = &data[0];
    data[x].threads = data;
    data[x].wantindex = -1;
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[0], work, &data[x]);
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  }
  struct timespec time = {
    1,
    0
  };
  struct timespec rem = {
    0,
    0
  };
  
  nanosleep(&time, &rem);
  for (int x = 0; x < threadsize ; x++) {
    data[x].running = 0;
    
  }
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  }
  printf("finished simulation.\n");
  long freq = 0;
  for (int x= 0; x < threadsize; x++) {
    freq += data[x].freq;
  }
  printf("freq: %ld\n", freq);
}