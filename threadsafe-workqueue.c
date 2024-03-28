#define _GNU_SOURCE
#include <err.h>
#include <errno.h>
#include <pthread.h>
#include <stdio.h> 
#include <time.h> 
#include <stdlib.h>
#include <string.h>
#include <math.h>

struct Work {
  int taskindex;
  int available __attribute__((aligned (128)));
};
struct Chunk {
  long start;
  long end;
  int available __attribute__((aligned (128)));
  int owner;
  int index;
};
#define FREE 1
#define READING 2
#define WRITING 3

#define READ_MASK (1 << 3)
#define WRITE_MASK (1 << 2)
#define BUSY_MASK (1)
#define PREP_READ_MASK (1 << 4)
#define PREP_WRITE_MASK (1 << 5)

// __attribute__((aligned (128)))
struct Data {
  long read;
  long write;
  int available;
  long start;
  long end;
  long ready;
  struct Data *main;
  struct Data *threads;
  struct Work *consumelist;
  long publishstart;
  long publishend;
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
  int readypublish;
  struct Chunk *freelist;
  struct Chunk *reading;
  struct Chunk *writing;

  long chunkslen;
  long chunksize;
  long newmask;
  long prev;



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
  int * available = calloc(data->chunkslen + 1, sizeof(long));
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  int * readywriters = calloc(data->threadsize, sizeof(int));
  data->workindex = bucketstart;
  int writers;
  int readers;
  int stop = 0;
  while (data->running == 1) {
    writers = 0;
    readers = 0;
    stop = 0;
    asm volatile ("" ::: "memory");
   // printf("write cycle\n");
    //memset(available, -1, data->threadsize);
    int availableidx = 0;
    if (data->threadindex == 0) {
      
      for (int x = 0; x < data->chunkslen + 1 ; x++) {
        
        if (data->freelist[x].available == FREE ) {
         available[availableidx] = x;
         availableidx++;


         // printf("%d chunk is free\n", x);
        }
      }
      if (availableidx == 0) {
       //printf("no chunks avail\n");
        
        continue;
      }
   
      
   //printf("buffers available %d\n", availableidx);
  for (int x = 1; x < data->threadsize ; x++) {
  // printf("thread %d %ld\n", x, data->threads[x].ready);
    long mask = data->threads[x].ready;
   // printf("pollpwrite?%d %ld\n", mask, (mask & PREP_WRITE_MASK));
        //printf("pollpread? %ld %ld\n", mask, (mask & PREP_READ_MASK));
       // printf("pplreadmask? %ld %ld\n", mask, (mask & READ_MASK));
      //  printf("pollwritemask ? %ld %ld\n", mask, (mask & WRITE_MASK));
        data->threads[x].newmask = 0;
        
        if ((data->threads[x].ready & WRITE_MASK) == WRITE_MASK || data->threads[x].ready == 0) {
         //printf("found a writer\n");
          readywriters[writers++] = x;
        }
    if ((data->threads[x].ready & READ_MASK) == READ_MASK || data->threads[x].ready == 0) {
      readyreaders[readers++] = x;
    // printf("found a reader\n");
    }
      }
   //printf("%d readers %d writers\n", readers, writers);
      
      
  
      long size = data->main->write - data->main->read;
      long buckets = size / availableidx;
      long offset = data->read;
      int assignedchunk = 0;
      
        for (int x = 0; x < readers ; x++) {
          if (assignedchunk == availableidx) {
            printf("not enough space readers\n");
                  break;
          }
          int thread = readyreaders[x];
          //printf("%d %p\n", thread, &data->freelist[available[assignedchunk]]);
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
          chunk->available = READING;
          //printf("assign %p\n", chunk);


          data->threads[thread].reading = chunk;
          
          chunk->owner = thread;
          long start = chunk->start;
          data->threads[thread].start = start;
          
          long end = chunk->end;
          data->threads[thread].end = end;
        // printf("reader giving %d between %ld and %ld\n", x, start, end);
          
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
       // printf("read newmask ORed with %d\n", data->threads[thread].newmask);
        }
      
   for (int x = 0; x < writers ; x++) {
                if (assignedchunk  == availableidx) {
                  
                 printf("not enough space writer %d %d\n", assignedchunk, availableidx);
                  break;
                }
          int thread = readywriters[x];
     
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
    
      chunk->available = WRITING;
          data->threads[thread].writing = chunk;
          chunk->owner = thread;
          long start = chunk->start;
          data->threads[thread].publishstart = start;
          
          long end = chunk->end;
          data->threads[thread].publishend = end;
        //  printf("writer giving %d between %ld and %ld\n", available[assignedchunk], start, end);
          // asm volatile ("sfence" ::: "memory");
     
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
     //printf("write newmask ORed with %ld\n", data->threads[thread].newmask);
        
   } 
      for (int x = 0; x < data->threadsize ; x++) {
        if (data->threads[x].newmask != 0) {
         // printf("thread %d %ld is now %ld\n", x, data->threads[x].ready, data->threads[x].newmask);
          data->threads[x].ready = data->threads[x].newmask;
          
        }
      }
      
  
    } else  {
      
      long mask = data->ready;
      
      if (mask != data->prev) {
//printf("pwrite?%d %ld\n", mask, (mask & PREP_WRITE_MASK));
       // printf("pread? %ld %d\n", mask, (mask & PREP_READ_MASK));
      //  printf("readmask? %ld %ld\n", mask, (mask & READ_MASK));
     //   printf("writemask ? %ld %ld\n", mask, (mask & WRITE_MASK));
      }
      data->prev = data->ready;
//printf("%d %d\n", mask, (mask & PREP_WRITE_MASK));
      long newmask = 0;
      if ((mask & PREP_READ_MASK) == PREP_READ_MASK) {
        
  /// printf("%d == %d\n", data->ready, PREP_READ_MASK);
      ///data->ready = BUSY_MASK;
   //  printf("consume %d %ld %ld\n", data->threadindex, data->start, data->end );
      for (int x = data->start; x < data->end; x++) {
     // printf("item\n");
        data->freq++;
        data->main->works[x].available = 0;
        
      }
       // printf("%p\n", data->reading);
        data->reading->available = FREE;
      // printf("%d freed\n", data->reading->index);
        newmask = newmask | READ_MASK;


      }
      if ((mask & PREP_WRITE_MASK) == PREP_WRITE_MASK) {
        
        //data->ready = BUSY_MASK;
      // printf("%d publishing\n", data->threadindex);
      
      
      if (data->publishstart < data->publishend) {
    //   printf("publish\n");
        for (int x = data->publishstart ; x < data->publishend; x++) {
          data->main->works[x].available = 1;
        }
      
        data->writing->available = FREE;
      //  printf("%d freed\n", data->writing->index);
        newmask = newmask | WRITE_MASK;
      }
        
      } 
      if (newmask != 0) {
       // printf("newmask %d\n", newmask);
        data->ready = newmask;
      }
     // asm volatile ("" ::: "memory");
    }
      
        
  }
      
        
  //memset(output, 0, 100);
   
    //if (data->threadindex == 0 && data->main->workindex >= data->worksize) {
    /*if (data->main->workindex >= data->worksize){
        data->main->workindex = 0;
        printf("work epoch end\n");
        for (int x = 0 ; x < data->worksize; x++) {
          data->main->works[x].available = 1;
        }
   }*/
      
   printf("%d thread exit\n", data->threadindex);           
}

int main(int argc, char **argv) {
  int debug = 0;
  int seconds = 5;
  int worksize_each = 1;
  int threadsize = 8;
  
  int workers = threadsize - 1;
  printf("read mask %d\n", READ_MASK);
  printf("write mask %d\n", WRITE_MASK);
  printf("prepwrite mask %d\n", PREP_WRITE_MASK);
  printf("Starting %d workers\n", threadsize);
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  
  long offset = 0;
  long chunkslen = ((threadsize - 1) * 2) + threadsize;
  int worksize = chunkslen * worksize_each;
  int buckets = worksize / threadsize;
  long chunksize = ceil((double) worksize / (double) chunkslen);
  struct Work *works = calloc(worksize, sizeof(struct Work));
  printf("Buffer size %d\n", worksize);
  int chunkindex = 0;
  struct Chunk *freelist = calloc(chunkslen, sizeof(struct Chunk));
          for (int x = 0; x < chunkslen; x++) {
          int thread = x;
        
          
          long start = offset;
          
          
          long end = start + chunksize;
          
          printf("writer giving %d between %ld and %ld\n", x, start, end);
          offset += chunksize;
        
         freelist[chunkindex].index = chunkindex;   freelist[chunkindex].available = FREE;
            freelist[chunkindex].start = start;
freelist[chunkindex].end = end;
            chunkindex++;
        }

printf("%ld chunks\n", chunkslen);
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
    data[x].ready = 0;
    data[x].availables = buckets;
    data[x].threadsize = threadsize;
    data[x].buckets = buckets;
    data[x].main = &data[0];
    data[x].threads = data;
    data[x].wantindex = -1;
    data[x].read = 0;
    data[x].write = worksize;
    
    data[x].freelist = freelist;
    data[x].chunksize = chunksize;
    data[x].chunkslen = chunkslen;
    data[x].newmask = 0;
    
  } 
  
  for (int x = 0; x < threadsize ; x++) {
    pthread_create(&thread[x], &attr[0], work, &data[x]);
    pthread_setaffinity_np(thread[x], sizeof(data[x].cpu_set), data[x].cpu_set);
  }
  
  struct timespec time = {
    seconds,
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
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  for (int x= 0; x < threadsize; x++) {
    freq += data[x].freq;
  }
  printf("freq: %ld\n", freq / seconds);
}