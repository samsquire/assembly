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
#include <limits.h>
#include <stddef.h>
#include <stdint.h>

#define NEW_EPOCH 1
 
#define DURATION 1
#define SAMPLE 0
#define THREADS 15
#define PRINT 0
#define ACCESSLOG 0


struct Cursor {
  int global;
  int cursor;
  int thread;
};

struct Access {
  int stream;
  int global;
  int cursor;
  int thread;
  int set;

};

struct CoroutineData {
  int running;
};

struct Scheduler {
  uint64_t rsp;
};

struct Coroutine {
  int index;
  uint64_t rsp;
  uint64_t eip;
  struct CoroutineData * data;
};

extern int switch_to(struct Coroutine * coroutines, int index, struct Scheduler * scheduler);

struct Epoch {
  int thread;
  struct timespec time;
  long buffer;
  int kind;
  int set;
  int dest;
  int stream;
};

int yield() {
  
}

int coroutine_func(struct Scheduler * scheduler, struct Coroutine* coroutine, struct CoroutineData * data) {
 // printf("%p %p %p coroutine running\n", scheduler, coroutine, data);


  while (data->running == 1) {
   asm("lea 0(%%rip), %%r11\n"
      "movq %%r11, %0" : "=rm" (coroutine->eip) ::"r11");
    // yield(1, scheduler, coroutine);
    printf("%ld\n", coroutine->eip);
  
  }
  //printf("loop finished\n");
  return 0;


}



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
  
  
  int running;
  int worksize;
  int threadindex;
  int threadsize;
  char *works;
  cpu_set_t *cpu_set;
  int loglevel;
  int *primes;
  int buckets;
  int availables;
  int bucketstart;
  
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
  int writecursor __attribute__((aligned (128)));
  int middle;
  int readcursor __attribute__((aligned (128)));
  int owritecursor;
  int oreadcursor;
  int step;
  int readstep;
  int globalstep;
  int * readcursors;
  int * writecursors;
  long currentread __attribute__((aligned (128)));
  long currentwrite __attribute__((aligned (128)));
  long prevread;
  long prevwrite;
  struct Epoch * epochs;
  int epochssize;
  int currentepoch;
  int thiswrite;
  struct Epoch * writelog;
  long totalwrites;
  long totalreads;
  struct Cursor * globalread;
  long * globalwrite __attribute__((aligned (128)));
  int lastgroup;
  int mystream;
  int laststream;
  long successreads;
  struct Access * reads;
  struct Access * writes;
  int cwrite;
  int cread;
  int accesssize;
  struct Coroutine * coroutines;
  struct Scheduler * scheduler;
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

int singlewriter3(struct Data *data, long * available, int * readyreaders, int * readywriters) {
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



  //printf("%d %d\n", data->writecursor, data->writecursor % (data->threadsize - 1));
  if (data->writecursor != 0 && (data->writecursor % (data->threadsize - 1)) == 0) {
    //data->currentwrite++;
   // data->writecursor = 0;
    //printf("writeepoch\n");
  } else {

  }

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


//if ((__atomic_load_n(&data->readcursor, __ATOMIC_SEQ_CST) % data->threadsize) == 0) {
   if (data->readcursor != 0 && (data->readcursor % (data->threadsize - 1)) == 0) {
    //data->currentread++;
   // data->readcursor = 0;
    //printf("readepoch\n");
    
  
        // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
        struct Data * thread = &data->threads[data->threadindex];
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
        epoch->kind = NEW_EPOCH;
        epoch->thread = data->threadindex;
        epoch->set = 1;
    
  } else {
    
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
  int cursorlimit = 5;
  int epochsize = 1;
  int epochwidth = 0xff;
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
  struct timespec time;
  
  long buffer;
  //printf("pw %ld %ld\n", data->main->currentwrite, data->prevwrite);
  //long lastwrite = __atomic_load_n(&data->main->currentwrite, __ATOMIC_ACQUIRE);

//printf("%ld %ld w%d\n", lastwrite, data->prevwrite, data->threadindex);
 //if (lastwrite != data->prevwrite) {
   
    uint64_t rsp;
    asm( "mov %%rsp, %0" : "=rm" ( rsp ));
  data->scheduler->rsp = rsp;
  //printf("%%rsp %p\n", (void *)rsp);
  // switch_to(struct Coroutine * coroutines, int index
  //printf("table %x\n", (void *)data->coroutines);
  //printf("coroutine 0 %x\n", &data->coroutines[0]);
 // printf("coroutine eip %lx\n", data->coroutines[0].eip);
 // printf("coroutine data %lx\n", data->coroutines[0].data);
  switch_to(data->coroutines, 0, data->scheduler);
 // printf("finished coroutine\n");
  //printf("%ld %ld w%d\n", lastwrite, data->prevwrite, data->threadindex);
 
     
clock_gettime(CLOCK_MONOTONIC_RAW, &time);
  //if (data->threadindex % 2 == 0) {
   
  if (data->running == 2) {
  //if (data ->threadindex == 0 ) {
     
     
   for (int x = 0 ; x < data->threadsize ; x++) {
      
    int global = (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth;
    
      //  buffer = data->mystream << 24 | ( global << 16) | data->threadindex << 8 | data->writecursor % 0xff;
    int cursor = data->writecursor;
    //cursor = 0;
     buffer = data->mystream << 24 | ( global << 16) | cursor % 0xff;

    if (ACCESSLOG == 1) {
struct Access * access = &data->writes[data->cwrite];
    access->stream = data->mystream;
    access->thread = data->threadindex;
    access->global = global;
    access->cursor = data->writecursor % 0xff; 
    access->set = 1;

    data->cwrite = (data->cwrite + 1) % data->accesssize;

    }
   // data->writecursor = (data->writecursor + 1) % 10;
    if (data->threadindex == 1) {
    //printf("w %d %d %d\n", data->mystream,  (data->main->globalwrite[data->mystream * 128] / (epochsize)) % epochwidth, data->writecursor);
    }
   /*
    while (data->main->works[buffer] != -1 && data->writecursor < 0xffff) { 
      data->writecursor = (data->writecursor + 1) % 0xffff;
      buffer = data->mystream << 24 | ( (data->main->globalwrite[data->mystream * 128] / (data->threadsize)) % 0xff) << 16 | data->writecursor;
    }
    */
      // printf("%x\n", buffer);
        // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
  struct Data * thread = &data->threads[data->threadindex];
  
  if (SAMPLE == 1) {

        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
        epoch->time = time;
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
        epoch->thread = data->threadindex;
 // epoch->dest = x;
  epoch->buffer = buffer;
  epoch->set = 1;
  }
    
     // printf("alrrady filled\n");
  if (data->main->works[buffer] != -1) {
    
    data->freq_writes++;
  }
  data->main->works[buffer] = data->threadindex;
        
  
        // data->readcursors[data->threadindex]++;
  // }
         
         
  //  data->prevread = data->main->currentread;
     
     
    data->writecursor = (data->writecursor + 1) % cursorlimit;
    
   }
      
    __atomic_fetch_add(&data->main->globalwrite[data->mystream * 128], 1, __ATOMIC_RELAXED);
//}
  } 
  ///else {
  long thisgroup = data->main->globalwrite[data->mystream * 128] / epochsize;
  
  if (thisgroup != data->lastgroup) {
     // printf("ndw group\n");
      data->writecursor = 0;
  }
  //printf("%d %d %d w\n", data->mystream, data->main->globalwrite[data->mystream * 128] % 0xff, data->threadindex);
 //data->mystream = (data->mystream + 1) % 8;
  //}
   
  
   if (thisgroup != data->lastgroup) {
     if (SAMPLE == 1) {
      // printf("epoch\n");
             struct Data * thread = &data->threads[data->threadindex];
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
        epoch->kind = NEW_EPOCH;
        epoch->thread = data->threadindex;
        epoch->stream = data->mystream;
        epoch->set = 1;
     }
   }
   data->lastgroup = thisgroup;

   //  __atomic_fetch_add(&data->main->totalwrites, 1, __ATOMIC_ACQUIRE);
  /*
    if (data->main->globalwrite != 0 && (data->main->globalwrite % (data->threadsize)) == 0) {
    //data->currentwrite++;
      __atomic_store_n(&data->main->globalwrite, 0, __ATOMIC_RELEASE);
    //printf("writeepoch\n");
  } else {

    }
    */
  //}
  
 //if (lastread != data->prevread)
 // {
   //printf("%ld  %ld r%d\n", data->main->currentread, data->prevread, data->threadindex);
  long thiswrite = data->main->globalwrite[data->laststream * 128];
  
  if (data->globalread[data->laststream].global < thiswrite || thiswrite == 0) {  
    for (int x = 0; x < data->threadsize - 1; x++) {
  // printf("%d\n", thiswrite);
   data->freq++;
  
        
      
          
            
           long past = (((data->globalread[data->laststream]).global / (epochsize)) - 1) % epochwidth;
        //long past = (((data->globalread[data->laststream]).global % epochwidth;
            if (past < 0) {
              past = 0;
            }
            
            // long buffer = (data->threadindex << 24) | (data->main->globalwrite % 0xf) << 16 | (data->main->writecursor % 0xf);
        
       // buffer = data->laststream << 24 | (past << 16) | data->globalread[data->laststream].thread << 8, data->globalread[data->laststream].cursor % 0xff;
    int cursor = data->globalread[data->laststream].cursor;
    //cursor = 0;
    buffer = data->laststream << 24 | (past << 16) | cursor % 0xff;
    
  if (ACCESSLOG == 1) {
    struct Access * access = &data->reads[data->cread];
    access->stream = data->laststream;
    access->thread = data->threadindex;
    access->global = past;
    access->cursor = data->globalread[data->laststream].cursor % 0xff;
    access->set = 1;
    data->cread = (data->cread + 1) % data->accesssize;
  }
    
    int thistream = data->laststream; 
    //buffer = data->laststream << 24 | (past << 16) | 0 % 0xff;
    if (data->threadindex == 1) {
          //printf("r %d %d %d %d\n", data->laststream, past, data->globalread[data->laststream].cursor, data->main->works[buffer]);
    }
    //printf("%d\n", data->readcursor);
    //printf("laststream %d\n", data->laststream);
      if (SAMPLE == 1) {
struct Data * thread = &data->threads[data->threadindex];
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
        epoch->time = time;
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
        epoch->thread = data->threadindex;
 // epoch->dest = x;
  epoch->buffer = buffer;
  epoch->set = 1;
      }
               // printf("%x\n", buffer);
                // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
                //&data->threads[data->threadindex];

        // printf("%d\n", data->main->works[buffer]);
    
        if (data->main->works[buffer] != -1) {
          data->successreads++;
          
          data->main->works[buffer] = -1;
          if (PRINT == 1) {
        printf("%d received bcast %d from %d\n", data->threadindex, data->main->works[buffer], data->readcursor);
          }
        }
    
         
          //printf("%d %d\n", data->threadindex, (data->main->currentread % data->threadsize) + data->oreadcursor + data->readcursor);
                // data->readcursors[data->threadindex]++;
          // }
                  // data->readcursor = (data->readcursor + 1) % 0xffffff;
        
        
    // how to count through the streams
    /*

    for (int stream = 0 ; stream < 5 ; stream++) {
      for (int global = 0 ; global < 0xff; global++) {
        for (int cursor = 0 ; cursor < data->threadsize ; cursor++) {
          
        }
      }
    }

    */
    
    // data->globalread[thistream].global++;
    
    
    
  
    
    
      
    
    if (data->globalread[thistream].cursor < cursorlimit) {
    
      data->globalread[thistream].global++;
        
        
      data->globalread[thistream].cursor = (data->globalread[thistream].cursor + 1);
      
      }
    
    if (data->globalread[thistream].cursor == cursorlimit) {
      
      data->laststream = (data->laststream + 1);
     // data->globalread[thistream].global++;
data->globalread[thistream].cursor = 0;
    }
    
    if (data->laststream == data->mystream) {
      data->laststream = data->laststream + 1;
     // data->globalread[data->laststream].cursor = 0;
    }
    if (data->laststream == 5) {
       data->laststream = 1;
      
       // printf("%d\n", data->laststream);
     }
    
  }
 // }
    //data->globalread[thistream].cursor = (data->globalread[thistream].cursor + 1);
    // data->globalread[thistream].cursor = data->globalread[thistream].cursor % cursorlimit;
    
         
      
      
    
    //printf("%ld\n", data->main->currentread);
      
 
}
    //__atomic_fetch_add(&data->main->globalread, 1, __ATOMIC_RELAXED);
      
//>writecursor, 1, __ATOMIC_RELAXED);
 // __atomic_fetch_add(&data->main->totalreads, 1, __ATOMIC_ACQUIRE);
 // }
  /*


     if (data->main->globalread != 0 && (data->main->globalread % (data->threadsize)) == 0) {
    //data->currentread++;
       __atomic_store_n(&data->main->globalread, 0, __ATOMIC_RELEASE);
    //data->readcursor = 0;
    //printf("readepoch\n");
    
  
        // printf("%d buffer %d %d\n", data->threadindex, buffer, data->readcursor);
        struct Data * thread = &data->threads[data->threadindex];
        struct Epoch * epoch = &thread->epochs[thread->currentepoch];
        clock_gettime(CLOCK_MONOTONIC_RAW, &epoch->time);
  thread->currentepoch = (thread->currentepoch + 1) % thread->epochssize;
        epoch->kind = NEW_EPOCH;
        epoch->thread = data->threadindex;
        epoch->set = 1;
    
  } else {
    
     } */
        // clock_gettime(CLOCK_MONOTONIC_RAW, &data->main->works[x].read);
        
      
       // printf("%p\n", data->reading);
        
    

      
      
      
        
        //data->ready = BUSY_MASK;
      // printf("%d publishing\n", data->threadindex);
      
      
      
      // printf("publish\n");
       
     // if (data->writecursors[data->threadindex] != data->middle ) {
  /*
          data->main->works[(data->main->currentwrite % data->threadsize) + data->owritecursor + data->writecursor].available = 1;
          data->freq_writes++;
          // data->writecursors[data->threadindex]++;
     //}  
        data->writecursor++;
        data->prevwrite = data->main->currentwrite;
        __atomic_fetch_add(&data->main->writecursor, 1, __ATOMIC_ACQUIRE);
        
       */
       
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
  
  
  int found = 0;
  int currentbucket = (data->threadindex + 1) % data->threadsize;
  int innerfind = 0;
  
  
  
  
  long * available = calloc(data->chunkslen + 1, sizeof(long));
  int * readyreaders = calloc(data->threadsize, sizeof(int));
  int * readywriters = calloc(data->threadsize, sizeof(int));
  
  
  int stop = 0;
  while (data->running > 0)  {
    writers = 0;
    readers = 0;
    stop = 0;
    asm volatile ("":"=m" (data->running)::);
   // printf("write cycle\n");
    //memset(available, -1, data->threadsize);

      threadwork(data);
    
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
  int seconds = DURATION;
  int worksize_each = 1;
  int threadsize = THREADS;
  
  int workers = threadsize - 1;
  printf("read mask %d\n", READ_MASK);
  printf("write mask %d\n", WRITE_MASK);
  printf("prepwrite mask %d\n", PREP_WRITE_MASK);
  printf("Starting %d workers\n", threadsize);
  pthread_t *thread = calloc(threadsize, sizeof(pthread_t));
  pthread_attr_t *attr = calloc(threadsize, sizeof(pthread_attr_t));
  struct Data *data = calloc(1, sizeof(struct Data) * threadsize);
  
  long offset = 0;
  long chunkslen = 0xffffffff;
  long worksize = chunkslen * worksize_each;
  int buckets = worksize / threadsize;
  long chunksize = ceil((double) worksize / (double) chunkslen);
  char *works = calloc(worksize, sizeof(char));
  memset(works, -1, worksize);
  printf("Buffer size %ld\n", worksize);
  int chunkindex = 0;
  int * readcursors = calloc(threadsize, sizeof(int));
  int * writecursors = calloc(threadsize, sizeof(int));
  struct Chunk *freelist = calloc(100, sizeof(struct Chunk));

printf("offset %ld\n", offset);
  
printf("%ld chunks\n", chunkslen);
 // for (int i = 0; i < worksize; i++) {
   // works[i].taskindex = 2;
   //works[i].available = 1;
    
 // }
  int cpu = 0;
  int * readies __attribute__((aligned (128))) = calloc(threadsize, sizeof(int));
  
  long * globalwrite;
  posix_memalign((void **)&globalwrite, 128, 128 * 4);
  struct Cursor * globalread = calloc(threadsize, sizeof(struct Cursor));
  data[0].works = works;
  int accesssize = 100000000;
  struct Access * reads = calloc(accesssize, sizeof(struct Access));
  struct Access * writes = calloc(accesssize, sizeof(struct Access));

  struct Scheduler * scheduler = calloc(1, sizeof(struct Scheduler));

  
  
  for (int x = 0; x < threadsize ; x++) {
    
    struct Coroutine * cos = calloc(10, sizeof(struct Coroutine));
    
    data[x].coroutines = cos;
    for (int y= 0; y < 10; y++ ) {
      struct CoroutineData * codata = calloc(1, sizeof(struct CoroutineData));
      cos[y].data = codata;
      cos[y].eip = (uint64_t)coroutine_func;
    } 
    data[x].scheduler = scheduler;
    data[x].reads = reads;
    data[x].writes = writes;
    data[x].cpu_set = calloc(1, sizeof(cpu_set_t));
    CPU_SET(cpu += 1, data[x].cpu_set);
    printf("assigning thread %d to cpu %d\n", x, cpu);
    data[x].bucketstart = x * buckets ;
    data[x].globalwrite = globalwrite;
    data[x].loglevel = debug;
    data[x].running = 2;
    data[x].threadindex = x;
    data[x].worksize = worksize;
    
    data[x].availables = buckets;
    data[x].threadsize = threadsize;
    data[x].readies = readies;
    data[x].readies[x] = 0;
    data[x].buckets = buckets;
    data[x].main = &data[0];
    data[x].threads = data;
    
    data[x].read = 0;
    data[x].write = worksize;
    data[x].readcursor = threadsize - 1;
    data[x].writecursor = 0;
    data[x].freelist = freelist;
    data[x].chunksize = chunksize;
    data[x].chunkslen = chunkslen;
    data[x].newmask = 0;
    data[x].prevread = threadsize;
    data[x].prevwrite = threadsize;
    data[x].mystream = 1 + (x / 4);
    data[x].thiswrite = threadsize;
    int epochs = 10000000;
    data[x].epochs = calloc(epochs, sizeof(struct Epoch));
    data[x].epochssize = epochs;
    data[x].globalread = globalread;
    data[x].writelog = calloc(10000, sizeof(struct Epoch));
    data[x].accesssize = accesssize;
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
  
  printf("runphased\n");
  for (int x = 0; x < threadsize ; x++) {
    data[x].running--;
    
  }
  
 printf("draining\n");
 // time.tv_sec = 3;
//nanosleep(&time, &rem);
  for (int x = 0; x < threadsize ; x++) {
    data[x].running--;
  }
  
  //nanosleep(&time, &rem);
  for (int x = 0; x < threadsize; x++) {
    void *res;
    pthread_join(thread[x], &res);
  }
  asm volatile ("" ::: "memory");
  printf("finished simulation.\n");
  long freq = 0;
  long sends = 1;
  for (int x = 0; x < threadsize; x++) {
    printf("%ld reads\n", data[x].freq);
    freq += data[x].freq;
  }
  printf("freq: %ld\n", freq/ seconds);
  printf("freq_ps: %ld\n", (freq*sends)/ seconds);
  printf("freq latency2: %ld\n", 1000000000/((freq/seconds)));
  printf("freq per thread latency: %ld\n", ((1000000000/(freq/seconds))/sends));
  printf("freq latency: %ld\n", 1000000000/((freq*sends)/seconds));
  
  long goods = 0;

  for (int x = 0; x < threadsize; x++) {
    printf("%ld successreads\n", data[x].successreads);
    goods += data[x].successreads;
  }
  
  long freq_writes = 0;
  
  for (int x = 0; x < threadsize; x++) {
    freq_writes += data[x].freq_writes;
    printf("%ld writes\n", data[x].freq_writes);
  }
  printf("freq_writes: %ld\n", freq_writes / seconds);

  printf("freq_writes_total: %ld\n", (freq_writes * sends) / seconds);
  printf("freq_writes latency2: %ld\n", 1000000000/(freq_writes / seconds));
  printf("freq_writes per thread latency: %ld\n", (1000000000/(freq_writes / seconds)) / sends);
  printf("freq_writes latency: %ld\n", 1000000000/((freq_writes * sends) / seconds));
  // printf("total_sent per second %ld\n", (freq * threadsize) / seconds);
  //printf("total_received per second %ld\n", (freq_writes * threadsize) / seconds);
  /*
  for (int i = 0; i < threadsize * 2; i++) {
   struct timespec created = works[i].created;
    struct timespec read = works[i].read;
    struct timespec written = works[i].written;
    printf("%ldns\n", read.tv_nsec - created.tv_nsec);
    printf("%ldns\n", written.tv_nsec - read.tv_nsec);
    
  }
  */
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
  printf("%ld good reads per second\n", goods / seconds);
  printf("%ld good reads per second latency\n", 1000000000 / (goods / seconds));
  if (SAMPLE == 1) {
    printf("creating sample log\n");
  char * filename = calloc(100, sizeof(char));
  char * buf = calloc(1000, sizeof(char));
  memset(filename, 0, 100);
  snprintf(filename, 100, "samples");
  FILE *out_file = fopen(filename, "w");
  
  for (int x = 0; x < threadsize; x++) {
    for (int y = 0; y < data[x].epochssize; y++) {
      struct Epoch * epoch = &data[x].epochs[y];
      if (epoch->set == 1) {
        memset(buf, 0, 1000);
        snprintf(buf, 100, "%ld%ld %d %d %ld %d %d\n", epoch->time.tv_sec, epoch->time.tv_nsec, epoch->kind, epoch->stream, epoch->buffer, epoch->thread, epoch->dest);
        fprintf(out_file, "%s", buf);
      }
    }
  }
    fclose(out_file);
  }
  /*
  for (int x = 0 ; x < worksize ; x++) {
    if (works[x] != -1) {
      //printf("unread work\n");
    }
  } */

 if (ACCESSLOG == 1) {
   printf("creating access log\n");
   char * filename = calloc(100, sizeof(char));
  char * buf = calloc(1000, sizeof(char));
  memset(filename, 0, 100);
  snprintf(filename, 100, "accesslog");
  FILE *out_file = fopen(filename, "w");

     for (int x = 0; x < threadsize; x++) {
    for (int y = 0; y < data[x].accesssize; y++) {
      struct Access * access = &data[x].reads[y];
      if (access->set == 1) {
        memset(buf, 0, 1000);
        snprintf(buf, 100, "r %d %d %d\n", access->stream, access->global, access->cursor);
        fprintf(out_file, "%s", buf);
      }
    }
       for (int y = 0; y < data[x].accesssize; y++) {
      struct Access * access = &data[x].writes[y];
      if (access->set == 1) {
        memset(buf, 0, 1000);
        snprintf(buf, 100, "w %d %d %d\n", access->stream, access->global, access->cursor);
        fprintf(out_file, "%s", buf);
      }
       }
     }
   fclose(out_file);
   
 }

  char * filename = calloc(100, sizeof(char));
  char * buf = calloc(1000, sizeof(char));
  memset(filename, 0, 100);
  snprintf(filename, 100, "coroutine.struct");
  FILE *out_file = fopen(filename, "w");

memset(buf, 0, 1000);
  snprintf(buf, 100, "index %ld\n", offsetof(struct Coroutine, index));
  fprintf(out_file, "%s", buf );
  
  memset(buf, 0, 1000);
  snprintf(buf, 100, "rsp %ld\n", offsetof(struct Coroutine, rsp));
  fprintf(out_file, "%s", buf );
  
  memset(buf, 0, 1000);
  snprintf(buf, 100, "eip %ld\n", offsetof(struct Coroutine, eip));
  fprintf(out_file, "%s", buf );


  memset(buf, 0, 1000);
  snprintf(buf, 100, "data %ld\n", offsetof(struct Coroutine, data));
  fprintf(out_file, "%s", buf);

  memset(buf, 0, 1000);
  snprintf(buf, 100, "corourinedata.running %ld\n", offsetof(struct CoroutineData, running));
  fprintf(out_file, "%s", buf);
  
  
  fclose(out_file);
}