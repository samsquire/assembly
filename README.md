# multithreaded barrier-runtime

This is the lock free algorithm for nonblocking multithreaded performant barrier:

The data races reported by Thread Sanitizer do not affect correctness but allow this algorithm to be extextremely performant this is because there is a happens before relationship between arrived and writes always come from the same thread.

```
void* barriered_thread(void *arg) {
  struct KernelThread *data = arg;
  // printf("In barrier task %d\n", data->thread_index);
  int t = 0;
  while (data->running == 1) {
    if (t >= data->task_count) {
      t = 0;
    }
    // printf("%d reporting %d %d\n", data->thread_index, t, data->task_count);
    for (; t < data->task_count; t++) {
      // printf("%d %d\n", data->thread_index, t);
      if (data->tasks[t].available == 1) {
        int previous = t;
        if (t > 0) {
          previous = t - 1;
        } else {
          previous = data->task_count - 1;
        }
        int arrived = 0; 
        for (int thread = 0 ; thread < data->thread_count; thread++) {
          // printf("thread %d does %d %d %d == %d\n", data->thread_index, t, previous, data->threads[thread].tasks[previous].arrived, data->tasks[t].arrived);
          if (data->threads[thread].tasks[previous].arrived == data->tasks[t].arrived) {
            arrived++;
          } 
        } 
        if (arrived == 0 || arrived == data->thread_count) {
          // we can run this task

          data->tasks[t].available = 0;

          data->tasks[t].run(&data->threads[data->thread_index].tasks[t]);
          data->tasks[t].arrived++;
          asm volatile ("mfence" ::: "memory");
        } else {
          // printf("%d %d %d\n", data->thread_index, t, arrived);
          break;
        }   
      } else {
      }
    }
  } 
  return 0;
}
```

This is what the work task looks like:

```
int barriered_work(volatile struct BarrierTask *data) {
  // printf("In barrier work task %d %d\n", data->thread_index, data->task_index);
  // printf("%d Arrived at task %d\n", data->thread_index, data->task_index);
  volatile long *n = &data->n;
  // we are synchronized
  char message[200];
  memset(&message, '\0', 200);

  sprintf(message, "Sending message from thread %d task %d", data->thread_index, data->task_index);
  if (data->thread_index == data->task_index) {

      void * tmp; 
      int next_task = (data->task_index + 1) % data->task_count;
      // swap this thread's write buffer with the next task
      for (int y = data->thread_count ; y > 0 ; y--) {
        tmp = data->thread->threads[y].tasks[data->task_index].mailboxes->lower; 
        data->thread->threads[y].tasks[data->task_index].mailboxes->lower = data->thread->threads[y].tasks[data->task_index].mailboxes->higher;
        // printf("move this this task task_index %d higher to %d lower\n", data->task_index, data->task_index);
        data->thread->threads[y].tasks[data->task_index].mailboxes->higher = data->thread->threads[y].tasks[next_task].mailboxes->higher;
        //printf("move next %d higher to %d higher\n", next_task, data->task_index);
        data->thread->threads[y].tasks[next_task].mailboxes->lower = tmp;
        // printf("move my %d lower to next %d lower\n",data->task_index, next_task);
      }

    struct Data *me = data->mailboxes->lower;
    for (int x = 0 ; x < me->messages_count ; x++) {
      data->sends++;
      // printf("%s\n", me->messages[x]);
    }
    me->messages_count = 0;

    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    int modcount = ++data->thread->protected_state->modcount;
    while (data->scheduled == 1) {
      data->n++;
      data->protected(&data->thread->threads[data->thread_index].tasks[data->task_index]);
    }
    if (modcount != data->thread->protected_state->modcount) {
      printf("Race condition!\n");
    }
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
  } else {
      while (data->scheduled == 1) {
        data->n++;
        struct Data *me = data->mailboxes->lower;
        if (me->messages_count < me->messages_limit) {

          me->messages[me->messages_count++] = message;
        } else {
          // printf("Starve!\n");
        }
      }
  }
  return 0;
}
```


This is what happens when all tasks are finished:

```
int barriered_reset(volatile struct BarrierTask *data) {
  // printf("In barrier reset task %d %d\n", data->thread_index, data->task_index);
    for (int x = 0 ; x < data->task_count ; x++) {
      // printf("Resetting %d %d\n", n, x);
      data->thread->threads[data->thread_index].tasks[x].arrived++; 
      // data->thread->tasks[x].arrived++; 
      
      data->thread->tasks[x].available = 1; 
  }
  asm volatile ("mfence" ::: "memory");
  return 0;
}
```
