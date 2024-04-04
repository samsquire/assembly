#define _GNU_SOURCE
#include <err.h>
#include <errno.h>
#include <pthread.h>
#include <stdio.h> 
#include <time.h> 
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <unistd.h>

struct Work {
  int taskindex;
  int available;
  struct timespec created;
  struct timespec read;
  struct timespec written;
};
struct Chunk {
  long start;
  long end;
  int available;
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
  int start;
  int end;
  int * readies;
  struct Data *main;
  struct Data *threads;
  struct Work *consumelist;
  int publishstart;
  int publishend;
  long freq;
  long freq_writes;
  int taskindex; 
  int workindex;
  int wantindex;
  int running;
  int worksize;
  int threadindex;
  int threadsize;
  struct Work *works;
  cpu_set_t *cpu_set;
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
  int newmask;
  long prev;
  struct timespec wstart;
  struct timespec wend;
  struct timespec wavail;
  struct timespec wpoll;
  struct timespec wassign;
  struct timespec swstart;
  struct timespec swend;
  int writecursor;
  int middle;
  int readcursor;
  int owritecursor;
  int oreadcursor;
  int step;
  int readstep;
  int globalstep;
  int * readcursors;
  int * writecursors;
  int currentread;
  int currentwrite;
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

int pollthreads(struct Data * data, int * readyreaders, int * readywriters, int * readers, int * writers) {
  long WM = WRITE_MASK;
  long RM = READ_MASK;
  for (int x = 1; x < data->threadsize ; x++) {
  // printf("thread %d %ld\n", x, data->threads[x].ready);
    int mask = data->threads[1].readies[x];
   // printf("pollpwrite?%d %ld\n", mask, (mask & PREP_WRITE_MASK));
        //printf("pollpread? %ld %ld\n", mask, (mask & PREP_READ_MASK));
       // printf("pplreadmask? %ld %ld\n", mask, (mask & READ_MASK));
      //  printf("pollwritemask ? %ld %ld\n", mask, (mask & WRITE_MASK));
       // data->threads[x].newmask = 0;
        
        if ((mask & WM) == WM || mask == 0) {
         //printf("found a writer\n");
          readywriters[(*writers)++] = x;
        }
    if ((mask & RM) == RM || mask == 0) {
      readyreaders[(*readers)++] = x;
    // printf("found a reader\n");
    }
      }
  // printf("%d readers %d writers\n", *readers, *writers);
      
  return 0;
}


int findavailable(struct Data * data, long * available, int * availableidx, int * readyreaders, int * readywriters) {
  for (int x = 0; x < data->chunkslen + 1 ; x++) {
        
        if (data->freelist[x].available == FREE ) {
          //printf("%d\n", *availableidx);
         available[*availableidx] = x;
         (*availableidx)++;
         if ((*availableidx) == data->threadsize * 2) {
           break;
         }

         // printf("%d chunk is free\n", x);
        }
      }
      if (*availableidx == 0) {
       //printf("no chunks avail\n");
        
        return 1;
      }
  return 0;
}

int singlewriter2(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  int completed = 0;
  /*
  for (int x = 1; x < data->threadsize; x++) {
    struct Data * t = &data->threads[x];
    
    if (t->readcursors[x] == t->middle) {
    //printf("%d\n", t->readcursor);
      int rc = t->oreadcursor;
      t->readcursors[x] = 0;
      completed++;
    } else {
      
    }
    
    if (t->writecursors[x] == t->middle) {
      int wc = t->owritecursor;
      t->writecursors[x] = 0;
      
    }
    
   
  }
  if (completed == data->threadsize) {
     data->globalstep = (data->globalstep + 1) % data->threadsize;
   }
   */
   
  if ((data->readcursor % data->threadsize) == 0) {
    data->currentread++;
    data->readcursor = 0;
    printf("readepoch\n");
  }
  if ((data->writecursor % data->threadsize) == 0) {
    data->currentwrite++;
    data->writecursor = 0;
    printf("writeepoch\n");
  }
  
}
/*
t0
thread1 r1 w2
thread2 r3 w4
thread3 r5 w6




*/

int singlewriter(struct Data *data, long * available, int * readyreaders, int * readywriters) {
  data->threads[0].step = (data->threads[0].step + 1) % data->threadsize;
  int readers = 0;
  int writers = 0;
  int availableidx = 0;
   /*
  readers = data->threadsize - 1;
  writers = data->threadsize - 1;
  for (int x = 1; x <data->threadsize; x++) {
    readyreaders[x] = x;
    readywriters[x] = x;
  }
  */
  //clock_gettime(CLOCK_MONOTONIC_RAW, &data->wstart);
  
  int fill = findavailable(data, available, &availableidx, readyreaders, readywriters);

//clock_gettime(CLOCK_MONOTONIC_RAW, &data->wavail);
  
  if (fill == 1) {
    return 1;
  }
      
   //printf("buffers available %d\n", availableidx);
 pollthreads(data, readyreaders, readywriters, &readers, &writers);
      
  //clock_gettime(CLOCK_MONOTONIC_RAW, &data->wpoll);
      
      int assignedchunk = 0;
      
        for (int x = 0; x < readers ; x++) {
          if (assignedchunk == availableidx) {
           // printf("not enough space readers\n");
                  break;
          }
          int thread = readyreaders[x];
          //printf("%d %p\n", thread, &data->freelist[available[assignedchunk]]);
          struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
          chunk->available = READING;
          //printf("assign %p\n", chunk);


          data->threads[thread].reading = chunk;
          
          chunk->owner = thread;
          int start = chunk->start;
          data->threads[thread].start = start;
          
          int end = chunk->end;
          data->threads[thread].end = end;
        // printf("reader giving %d between %ld and %ld\n", x, start, end);
        
         // clock_gettime(CLOCK_MONOTONIC_RAW, &data->main->works[start].created);
         data->threads[thread].newmask =  data->threads[thread].newmask | PREP_READ_MASK;
       // printf("read newmask ORed with %d\n", data->threads[thread].newmask);
        }
      
   for (int x = 0; x < writers ; x++) {
                if (assignedchunk  == availableidx) {
                  
                 //printf("not enough space writer %d %d\n", assignedchunk, availableidx);
                  break;
                }
          int thread = readywriters[x];
     
      struct Chunk *chunk = &data->freelist[available[assignedchunk++]];
    
      chunk->available = WRITING;
          data->threads[thread].writing = chunk;
          chunk->owner = thread;
          int start = chunk->start;
          data->threads[thread].publishstart = start;
          
          int end = chunk->end;
          data->threads[thread].publishend = end;
        //  printf("writer giving %d between %ld and %ld\n", available[assignedchunk], start, end);
          // asm volatile ("sfence" ::: "memory");
     
         data->threads[thread].newmask = data->threads[thread].newmask | PREP_WRITE_MASK;
     //printf("write newmask ORed with %ld\n", data->threads[thread].newmask);
        
   } 
      for (int x = 0; x < data->threadsize ; x++) {
        if (data->threads[x].newmask != 0) {
         // printf("thread %d %ld is now %ld\n", x, data->threads[x].ready, data->threads[x].newmask);
          data->threads[x].readies[x] = data->threads[x].newmask;
          
        }
      }
  // clock_gettime(CLOCK_MONOTONIC_RAW, &data->wassign);
  return 0;
}

int * threadwork(struct Data * data) {
 // printf("%d\n", data->threadindex);
   // asm volatile (""::: "memory");

//printf("%d %d\n", mask, (mask & PREP_WRITE_MASK));
      
      
        
  /// printf("%d == %d\n", data->ready, PREP_READ_MASK);
      ///data->ready = BUSY_MASK;
   //  printf("consume %d %ld %ld\n", data->threadindex, data->start, data->end );
      //printf("%d %d rc\n", data->readcursor, data->middle);
     // printf("%d \n", data->readcursor);
  
    // printf("item %d\n", x);
  //if (data->readcursors[data->threadindex] != data->middle) {
        data->freq++;
  int buffer = 1 * (data->main->currentread % data->threadsize) + 2 * data->oreadcursor + 3 * data->readcursor + 4 * data->threadindex;
  printf("%d buffer %d\n", data->threadindex, buffer);
        data->main->works[buffer].available = 0;
  //printf("%d %d\n", data->threadindex, (data->main->currentread % data->threadsize) + data->oreadcursor + data->readcursor);
        // data->readcursors[data->threadindex]++;
  // }
         __atomic_fetch_add(&data->main->readcursor, 1, __ATOMIC_ACQUIRE);
     
        // clock_gettime(CLOCK_MONOTONIC_RAW, &data->main->works[x].read);
        
      
       // printf("%p\n", data->reading);
        


      
      
      
        
        //data->ready = BUSY_MASK;
      // printf("%d publishing\n", data->threadindex);
      
      
      
      // printf("publish\n");
     
     // if (data->writecursors[data->threadindex] != data->middle ) {
          data->main->works[(data->main->currentwrite % data->threadsize) + data->owritecursor + data->writecursor].available = 1;
          data->freq_writes++;
          // data->writecursors[data->threadindex]++;
     //}  
        __atomic_fetch_add(&data->main->writecursor, 1, __ATOMIC_ACQUIRE);
       
          // clock_gettime(CLOCK_MONOTONIC_RAW, &data->main->works[x].written);
        
      
        
      //  printf("%d freed\n", data->writing->index);
        
      
        
      
      
     //asm volatile ("sfence" ::: "memory");
  
      
       
}

void * work2(void * arg) {
  struct Data *data = (struct Data*) arg;
  while (data->running == 1) {
    asm volatile ("" ::: "memory");
      data->freq++;
  }
  
}

void * work(void * arg) {
  
  int writers;
  int readers;
  struct Data *data = (struct Data*) arg;
  printf("started thread %d\n", data->threadindex);
  char * output = calloc(100, sizeof(char));
  
  int found = 0;
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  int innerfind = 0;
  int bucketlim = ((data->threadindex + 1) * data->buckets) ;
  int bucketstart = data->bucketstart;
  
  printf("bucketlim %d\n", bucketlim);
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  int * readywriters = calloc(data->threadsize, sizeof(int));
  data->workindex = bucketstart;
  
  int stop = 0;
  while (data->running == 1) {
    writers = 0;
    readers = 0;
    stop = 0;
    asm volatile ("":"=m" (data->running)::);
   // printf("write cycle\n");
    //memset(available, -1, data->threadsize);
    if (data->threadindex == 0) {
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swstart);
      singlewriter2(data, available, readyreaders, readywriters);
      clock_gettime(CLOCK_MONOTONIC_RAW, &data->swend);
  
    } else  {
      threadwork(data);
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
  long chunkslen = threadsize * (2 * threadsize) + threadsize;
  int worksize = chunkslen * worksize_each;
  int buckets = worksize / threadsize;
  long chunksize = ceil((double) worksize / (double) chunkslen);
  struct Work *works = calloc(worksize, sizeof(struct Work));
  printf("Buffer size %d\n", worksize);
  int chunkindex = 0;
  int * readcursors = calloc(threadsize, sizeof(int));
  int * writecursors = calloc(threadsize, sizeof(int));
  struct Chunk *freelist = calloc(chunkslen, sizeof(struct Chunk));
          for (int x = 0; x < threadsize; x++) {
            
          int thread = x;
               
          long start = offset;
          
          long middle = start + threadsize + 1;
          long end = middle + threadsize;
          
       //   printf("writer giving %d between %ld and %ld\n", x, start, end);
          offset += (threadsize * 2) + 1;
        
     data[chunkindex].writecursors = writecursors;
     data[chunkindex].readcursors = readcursors;
            
    data[chunkindex].owritecursor = middle + 1;
    printf("middle %ld\n", middle);
    data[chunkindex].middle = middle;
    data[chunkindex].readcursors[chunkindex] = middle;
    data[chunkindex].writecursors[chunkindex] = middle;
    data[chunkindex].oreadcursor = start;
    chunkindex++;
        
          }
printf("offset %d\n", offset);
  
printf("%ld chunks\n", chunkslen);
  for (int i = 0; i < worksize; i++) {
    works[i].taskindex = 2;
    works[i].available = 1;
    
  }
  int cpu = 0;
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
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
    data[x].readies = readies;
    data[x].readies[x] = 0;
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
    pthread_create(&thread[x], &attr[x], work, &data[x]);
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
  for (int x = 0; x < threadsize; x++) {
    printf("%ld\n", data[x].freq);
    freq += data[x].freq;
  }
  printf("freq: %ld\n", freq/ seconds);
  long freq_writes = 0;
  for (int x = 0; x < threadsize; x++) {
    freq_writes += data[x].freq_writes;
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);

  for (int i = 0; i < threadsize * 2; i++) {
   struct timespec created = works[i].created;
    struct timespec read = works[i].read;
    struct timespec written = works[i].written;
    printf("%ldns\n", read.tv_nsec - created.tv_nsec);
    printf("%ldns\n", written.tv_nsec - read.tv_nsec);
    
  }
  printf("writer speed\n");
  for (int x = 0; x < 1 ;  x++){
   printf("%ld\n", data[x].wend.tv_nsec - data[x].wstart.tv_nsec);
    printf("%ld\n", data[x].wavail.tv_nsec - data[x].wstart.tv_nsec);
    printf("%ld\n", data[x].wend.tv_nsec - data[x].wavail.tv_nsec);
    printf("%ld\n", data[x].wassign.tv_nsec - data[x].wpoll.tv_nsec);
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wassign.tv_nsec);
    printf("%ld\n", data[x].wpoll.tv_nsec - data[x].wavail.tv_nsec);
    printf("sw %ld\n", data[x].swend.tv_nsec - data[x].swstart.tv_nsec);
  } 
  
}