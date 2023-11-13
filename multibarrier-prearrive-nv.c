/*
Copyright (C) 2023 by Samuel Michael Squire sam@samsquire.com

Permission to use, copy, modify, and/or distribute this software for any purpose with or without fee is hereby granted.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

gcc barrier-runtime-server.c -o barrier-runtime-server -O3 -luring 
./barrier-runtime-server

Samuel Michael Squire's multithreaded barrier runtime
from https://github.com/samsquire/assembly

This multithreaded barrier runtime is Zero Clause BSD licenced.

Includes Samuel Michael Squire's nonblocking barrier ported from
Java to C. 

see https://github.com/samsquire/multiversion-concurrency-control
for Java version
NonBlockingBarrierSynchronizationPreempt.java

This program implements synchronization without mutexes on top of data races.
I rely on the fact that there is only one thread writing and
there can be any number of readers and stale reads
don't affect correctness.

Liburing HTTP server from https://github.com/shuveb/loti-examples/blob/master/webserver_liburing.c
MIT License

Copyright (c) 2020 Shuveb Hussain

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/
#define _GNU_SOURCE
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
#include <sched.h>
#define TIMER 0
#define WORKER 1
#define IO 2
#define EXTERNAL 3

#define DURATION 5
#define TICK 1000000L

#define QUEUE_DEPTH             256
#define READ_SZ                 8192

#define EVENT_TYPE_ACCEPT       0
#define EVENT_TYPE_READ         1
#define EVENT_TYPE_WRITE        2
#define SERVER_STRING           "Server: zerohttpd/0.1\r\n"

const char *unimplemented_content = \
                                "HTTP/1.0 400 Bad Request\r\n"
                                "Content-type: text/html\r\n"
                                "\r\n"
                                "<html>"
                                "<head>"
                                "<title>ZeroHTTPd: Unimplemented</title>"
                                "</head>"
                                "<body>"
                                "<h1>Bad Request (Unimplemented)</h1>"
                                "<p>Your client sent a request ZeroHTTPd did not understand and it is probably not your fault.</p>"
                                "</body>"
                                "</html>";

const char *http_404_content = \
                                "HTTP/1.0 404 Not Found\r\n"
                                "Content-type: text/html\r\n"
                                "\r\n"
                                "<html>"
                                "<head>"
                                "<title>ZeroHTTPd: Not Found</title>"
                                "</head>"
                                "<body>"
                                "<h1>Not Found (404)</h1>"
                                "<p>Your client is asking for an object that was not found on this server.</p>"
                                "</body>"
                                "</html>";
struct Buffers {
  int count; 
  struct Buffer *buffer;
};
struct Buffer {
  void * data; 
  int available;
};

struct Request {
    int event_type;
    int iovec_count;
    int client_socket;
    struct iovec iov[];
};

struct Mailbox {
  void *lower;
  void *higher;
  long sent;
  long received;
};

struct Data {
  struct Message **messages;
  long messages_count;
  long messages_limit;
};

struct Message {
  char * message;
  long thread_index;
  long task_index;
};

struct BarrierTask {
  int task_index;
  int rerunnable;
  int arrived __attribute__((aligned (128))); 
  int prearrive __attribute__((aligned (128))); 
  long n; 
  long v; 
  int (*run)(struct BarrierTask*);
  int (*protected)(struct BarrierTask*);
  struct KernelThread *thread;
  int thread_index;
  int thread_count;
  int available;
  int task_count;
  int scheduled;
  struct Snapshot *snapshots;
  long snapshot_count;
  long current_snapshot;
  long ingest_count;
  struct Mailbox *mailboxes;
  long sends;
  int sending;
  int worker_count;
  struct Message *message;
  int next_thread;
};
struct TaskSnapshot {
  struct timespec task_start ;
  struct timespec task_end ;
  int task;
};
struct KernelThread {
  int thread_index;
  int real_thread_index;
  int type; 
  int preempt_interval;
  struct KernelThread **threads;
  int thread_count;
  int total_thread_count;
  int my_thread_count;
  struct BarrierTask *tasks;
  int task_count;
  int running;
  struct ProtectedState *protected_state;
  struct Buffers *buffers;
  struct io_uring *ring;
  int _eventfd;
  struct timespec *start;
  struct timespec *end;
  long iteration_count;
  long timestamp_count;
  long timestamp_limit;
  struct TaskSnapshot *task_snapshot;
  long task_timestamp_count;
  long task_timestamp_limit;
  long cycles;
  cpu_set_t *cpu_set;
  int other;
};

struct ProtectedState {
  long protected;
  long balance;
  int modcount;
};

struct Snapshot {
  struct timespec start;
  struct timespec end;
};

void fatal_error(const char *syscall) {
    perror(syscall);
    exit(1);
}
void strtolower(char *str) {
    for (; *str; ++str)
        *str = (char)tolower(*str);
}
void *zh_malloc(size_t size) {
    void *buf = malloc(size);
    if (!buf) {
        fprintf(stderr, "Fatal error: unable to allocate memory.\n");
        exit(1);
    }
    return buf;
}
const char *get_filename_ext(const char *filename) {
    const char *dot = strrchr(filename, '.');
    if (!dot || dot == filename)
        return "";
    return dot + 1;
}
void send_headers(const char *path, off_t len, struct iovec *iov) {
    char small_case_path[1024];
    char send_buffer[1024];
    strcpy(small_case_path, path);
    strtolower(small_case_path);

    char *str = "HTTP/1.0 200 OK\r\n";
    unsigned long slen = strlen(str);
    iov[0].iov_base = zh_malloc(slen);
    iov[0].iov_len = slen;
    memcpy(iov[0].iov_base, str, slen);

    slen = strlen(SERVER_STRING);
    iov[1].iov_base = zh_malloc(slen);
    iov[1].iov_len = slen;
    memcpy(iov[1].iov_base, SERVER_STRING, slen);

    /*
     * Check the file extension for certain common types of files
     * on web pages and send the appropriate content-type header.
     * Since extensions can be mixed case like JPG, jpg or Jpg,
     * we turn the extension into lower case before checking.
     * */
    const char *file_ext = get_filename_ext(small_case_path);
    if (strcmp("jpg", file_ext) == 0)
        strcpy(send_buffer, "Content-Type: image/jpeg\r\n");
    if (strcmp("jpeg", file_ext) == 0)
        strcpy(send_buffer, "Content-Type: image/jpeg\r\n");
    if (strcmp("png", file_ext) == 0)
        strcpy(send_buffer, "Content-Type: image/png\r\n");
    if (strcmp("gif", file_ext) == 0)
        strcpy(send_buffer, "Content-Type: image/gif\r\n");
    if (strcmp("htm", file_ext) == 0)
        strcpy(send_buffer, "Content-Type: text/html\r\n");
    if (strcmp("html", file_ext) == 0)
        strcpy(send_buffer, "Content-Type: text/html\r\n");
    if (strcmp("js", file_ext) == 0)
        strcpy(send_buffer, "Content-Type: application/javascript\r\n");
    if (strcmp("css", file_ext) == 0)
        strcpy(send_buffer, "Content-Type: text/css\r\n");
    if (strcmp("txt", file_ext) == 0)
        strcpy(send_buffer, "Content-Type: text/plain\r\n");
    slen = strlen(send_buffer);
    iov[2].iov_base = zh_malloc(slen);
    iov[2].iov_len = slen;
    memcpy(iov[2].iov_base, send_buffer, slen);

    /* Send the content-length header, which is the file size in this case. */
    sprintf(send_buffer, "content-length: %ld\r\n", len);
    slen = strlen(send_buffer);
    iov[3].iov_base = zh_malloc(slen);
    iov[3].iov_len = slen;
    memcpy(iov[3].iov_base, send_buffer, slen);

    /*
     * When the browser sees a '\r\n' sequence in a line on its own,
     * it understands there are no more headers. Content may follow.
     * */
    strcpy(send_buffer, "\r\n");
    slen = strlen(send_buffer);
    iov[4].iov_base = zh_malloc(slen);
    iov[4].iov_len = slen;
    memcpy(iov[4].iov_base, send_buffer, slen);
}
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    int fd;

    char *buf = zh_malloc(file_size);
    fd = open(file_path, O_RDONLY);
    if (fd < 0)
        fatal_error("read");

    /* We should really check for short reads here */
    int ret = read(fd, buf, file_size);
    if (ret < file_size) {
        fprintf(stderr, "Encountered a short read.\n");
    }
    close(fd);

    iov->iov_base = buf;
    iov->iov_len = file_size;
}
int add_write_request(struct Request *req, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    req->event_type = EVENT_TYPE_WRITE;
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    io_uring_sqe_set_data(sqe, req);
    io_uring_submit(ring);
    return 0;
}

int add_read_request(int client_socket, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
        

    req->iov[0].iov_base = malloc(READ_SZ);
    req->iov[0].iov_len = READ_SZ;
    req->event_type = EVENT_TYPE_READ;
    req->client_socket = client_socket;
    memset(req->iov[0].iov_base, 0, READ_SZ);
    /* Linux kernel 5.5 has support for readv, but not for recv() or read() */
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    io_uring_sqe_set_data(sqe, req);
    io_uring_submit(ring);
    return 0;
}
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    struct Request *req = zh_malloc(sizeof(*req) + sizeof(struct iovec));
    unsigned long slen = strlen(str);
    req->iovec_count = 1;
    req->client_socket = client_socket;
    req->iov[0].iov_base = zh_malloc(slen);
    req->iov[0].iov_len = slen;
    memcpy(req->iov[0].iov_base, str, slen);
    add_write_request(req, ring);
}
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    _send_static_string_content(unimplemented_content, client_socket, ring);
}
void handle_http_404(int client_socket, struct io_uring *ring) {
    _send_static_string_content(http_404_content, client_socket, ring);
}

void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    char final_path[1024];

    /*
     If a path ends in a trailing slash, the client probably wants the index
     file inside of that directory.
     */
    if (path[strlen(path) - 1] == '/') {
        strcpy(final_path, "public");
        strcat(final_path, path);
        strcat(final_path, "index.html");
    }
    else {
        strcpy(final_path, "public");
        strcat(final_path, path);
    }

    /* The stat() system call will give you information about the file
     * like type (regular file, directory, etc), size, etc. */
    struct stat path_stat;
    if (stat(final_path, &path_stat) == -1) {
        printf("404 Not Found: %s (%s)\n", final_path, path);
        handle_http_404(client_socket, ring);
    }
    else {
        /* Check if this is a normal/regular file and not a directory or something else */
        if (S_ISREG(path_stat.st_mode)) {
            struct Request *req = zh_malloc(sizeof(*req) + (sizeof(struct iovec) * 6));
            req->iovec_count = 6;
            req->client_socket = client_socket;
            send_headers(final_path, path_stat.st_size, req->iov);
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
            printf("200 %s %ld bytes\n", final_path, path_stat.st_size);
            add_write_request(req, ring);
        }
        else {
            handle_http_404(client_socket, ring);
            printf("404 Not Found: %s\n", final_path);
        }
    }
}

void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    char *method, *path, *saveptr;

    method = strtok_r(method_buffer, " ", &saveptr);
    strtolower(method);
    path = strtok_r(NULL, " ", &saveptr);

    if (strcmp(method, "get") == 0) {
        handle_get_method(path, client_socket, ring);
    }
    else {
        handle_unimplemented_method(client_socket, ring);
    }
}

int get_line(const char *src, char *dest, int dest_sz) {
    for (int i = 0; i < dest_sz; i++) {
        dest[i] = src[i];
        if (src[i] == '\r' && src[i+1] == '\n') {
            dest[i] = '\0';
            return 0;
        }
    }
    return 1;
}

int handle_client_request(struct Request *req, struct io_uring *ring) {
    char http_request[1024];
    /* Get the first line, which will be the request */
    if(get_line(req->iov[0].iov_base, http_request, sizeof(http_request))) {
        fprintf(stderr, "Malformed request\n");
        exit(1);
    }
    handle_http_method(http_request, req->client_socket, ring);
    return 0;
}

int add_accept_request(int socket, struct sockaddr_in *client_addr,
                       socklen_t *client_addr_len, struct io_uring *ring) {
  struct io_uring_sqe *sqe = io_uring_get_sqe(ring);

  io_uring_prep_accept(sqe, socket, (struct sockaddr *) client_addr,
                       client_addr_len, 0);
  struct Request *req = malloc(sizeof(*req));
  req->event_type = EVENT_TYPE_ACCEPT;
  io_uring_sqe_set_data(sqe, req);
  io_uring_submit(ring);
}

void* io_thread(void *arg) {
  int port = 6363;
  struct KernelThread *data = arg;
  struct io_uring ring = *data->ring;
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
  io_uring_register_eventfd(data->ring, 0);
  int sock;
  struct sockaddr_in srv_addr;

  sock = socket(PF_INET, SOCK_STREAM, 0);
  if (sock == -1)
      fatal_error("socket()");

  int enable = 1;
  if (setsockopt(sock,
                 SOL_SOCKET, SO_REUSEADDR,
                 &enable, sizeof(int)) < 0)
      fatal_error("setsockopt(SO_REUSEADDR)");


  memset(&srv_addr, 0, sizeof(srv_addr));
  srv_addr.sin_family = AF_INET;
  srv_addr.sin_port = htons(port);
  srv_addr.sin_addr.s_addr = htonl(INADDR_ANY);

  if (bind(sock,
           (const struct sockaddr *)&srv_addr,
           sizeof(srv_addr)) < 0)
      fatal_error("bind()");

  if (listen(sock, 10) < 0) {
    fatal_error("listen()");
  }
  
  printf("Listening on port %d\n", port);
    
  struct io_uring_cqe *cqe;
  struct sockaddr_in client_addr;
  socklen_t client_addr_len = sizeof(client_addr);

  add_accept_request(sock, &client_addr, &client_addr_len, &ring);

  eventfd_t dummy;
  struct iovec *iov = calloc(1, sizeof(struct iovec));
  iov->iov_base = zh_malloc(10);
  iov->iov_len = 10;
  struct io_uring_sqe *sqe= io_uring_get_sqe(&ring);
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
  io_uring_submit(&ring);
  while (data->running == 1) {
      printf("Looping server...\n"); 
      int ret = io_uring_wait_cqe(&ring, &cqe);
      if (cqe->user_data == 1) {
        io_uring_cqe_seen(&ring, cqe);
        printf("Received stop event\n");
        break;
      }
      printf("Received wait finished\n");
      struct Request *req = (struct Request *) cqe->user_data;
      if (ret < 0)
          fatal_error("io_uring_wait_cqe");
      if (cqe->res < 0) {
          fprintf(stderr, "Async request failed: %s for event: %d\n",
                  strerror(-cqe->res), req->event_type);
          exit(1);
      }

      switch (req->event_type) {
          case EVENT_TYPE_ACCEPT:
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
              add_read_request(cqe->res, &ring);
              free(req);
              break;
          case EVENT_TYPE_READ:
              if (!cqe->res) {
                  fprintf(stderr, "Empty request!\n");
                  break;
              }
              handle_client_request(req, &ring);
              free(req->iov[0].iov_base);
              free(req);
              break;
          case EVENT_TYPE_WRITE:
              for (int i = 0; i < req->iovec_count; i++) {
                  free(req->iov[i].iov_base);
              }
              close(req->client_socket);
              free(req);
              break;
      }
      /* Mark this request as processed */
      io_uring_cqe_seen(&ring, cqe);
      struct io_uring_sqe *sqe= io_uring_get_sqe(&ring);
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
      io_uring_submit(&ring);
    }
  
  printf("Finished io thread\n");
  return 0;
}

void* barriered_thread(void *arg) {
  struct KernelThread *data = arg;
  // printf("In barrier task %d\n", data->thread_index);
  // printf("TASK POINTER %p\n", data->threads[data->thread_index]->tasks);
  int t = 0;
  int waiting = 0;


  while (data->running == 1) {
    if (t >= data->task_count) {
      t = 0;
      data->cycles++;
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
        int prearrive = 0; 
        
        for (int thread = 0 ; thread < data->thread_count; thread++) {
          // printf("thread %d does %d %d %d == %d\n", data->thread_index, t, previous, data->threads[thread]->tasks[previous].arrived, data->tasks[t].arrived);
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
            arrived++;
          } 
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
            prearrive++;
          }
        } 
        if (prearrive == 0 || prearrive == data->thread_count) {
          if (waiting == 1) {
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
            waiting = 0; 
          }
        }
        if (arrived == 0 || arrived == data->thread_count) {
          data->tasks[t].prearrive++;
          // we can run this task
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
          }

          data->tasks[t].available = 0;
          // printf("In thread %d %d %d\n", data->thread_index, data->real_thread_index, t);
          // printf("TASK POINTER %p\n", data->threads[data->thread_index]->tasks);
          // printf("resolve %p %p %p my %d real %d task %d\n", &data->threads[data->thread_index], data->threads[data->thread_index]->tasks, &data->tasks, data->thread_index, data->real_thread_index, t);
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
          //if (t == data->thread_index) {
          //  data->tasks[t].protected(&data->threads[data->thread_index]->tasks[t]);
          //}
          data->tasks[t].arrived++;
          data->iteration_count++;
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
            data->timestamp_count = data->timestamp_count + 1;
          }
          asm volatile ("sfence" ::: "memory");
          if (waiting == 0) {
            data->task_snapshot[data->task_timestamp_count].task = t;
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
            waiting = 1;
          }
          // break;
        } else {
          // printf("%d %d %d\n", data->thread_index, t, arrived);
          break;
        }   
      } else {

           // printf("%d not available\n", t);
      }
    }
  } 
  return 0;
}

void* timer_thread(void *arg) {
  long tick = TICK;
  long tickseconds = 0;
  // long tick = 0L;
  long times = ((1000000000L*DURATION)/tick);
  // long times = tickseconds * 10;
  
  struct KernelThread *data = arg;
  printf("In timer task %d\n", data->thread_index);
  struct timespec rem;
  struct timespec rem2;
  struct timespec preempt = {
    tickseconds,
    tick };
  struct timespec req = {
    DURATION,
    0 };
  
  int y = 0;
  int n = 0;

  printf("Will sleep %ld times\n", times);
  while (data->running && n < times) {
    n++;
    nanosleep(&preempt , &rem2);
    // preempt tasks
    for (int x = 0 ; x < data->thread_count ; x++) {
        int next = (y + 1) % data->threads[x]->task_count;
        data->threads[x]->tasks[next].scheduled = 1;
        data->threads[x]->tasks[y].scheduled = 0;
    }
    asm volatile ("mfence" ::: "memory");
    y++;
    if (y >= data->threads[0]->task_count) {
      y = 0;
    }
  }
  
  printf("Finished, waiting for drain\n");
  // nanosleep(&req , &rem);
  for (int x = 0 ; x < data->total_thread_count ; x++) {
    for (int y = 0 ; y < data->task_count ; y++) {
      data->threads[x]->tasks[y].sending = 0;
    }
  }
  asm volatile ("mfence" ::: "memory");

  int drained = 0;  
  struct timespec drainrem;
  struct timespec drain = {
    1,
    0 };

  while (drained == 0) {
    // preempt tasks
    for (int x = 0 ; x < data->thread_count ; x++) {
        int next = (y + 1) % data->threads[x]->task_count;
        data->threads[x]->tasks[next].scheduled = 1;
        data->threads[x]->tasks[y].scheduled = 0;
    }
    asm volatile ("mfence" ::: "memory");
    y++;
    if (y >= data->threads[0]->task_count) {
      y = 0;
    }
    int all_empty = 1;
    for (int x = 0 ; x < data->my_thread_count ; x++) {
      for (int y = 0 ; y < data->my_thread_count ; y++) {
        for (int k = 0 ; k < data->my_thread_count; k++) {
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
            all_empty = 0;
            printf("%d %ld %ld left\n", k, ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count, ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count);
            // printf("Someone unfinished\n");
            break;
          }
        }
      }
    }
    if (all_empty == 1) {
      drained = 1;
    } else {
      nanosleep(&drain , &drainrem);
    }
  }
  
  printf("Finished\n");
  while (data->running) {
    // nanosleep(&req , &rem);
    for (int x = 0 ; x < data->total_thread_count ; x++) {
      data->threads[x]->running = 0;
      if (data->threads[x]->type == IO) {
        printf("Stopping io_uring\n");
        eventfd_write(data->threads[x]->_eventfd, 1);
      }
    }
    // forcefully deschedule all tasks
    for (int x = 0 ; x < data->thread_count ; x++) {
      for (int y = 0 ; y < data->task_count ; y++) {
        data->threads[x]->tasks[y].scheduled = 0;
      }
    }
    asm volatile ("mfence" ::: "memory");
    printf("Slept \n");
    data->running = 0;
  }
  printf("Timer thread stopping\n");
  return 0;
}

void * external_thread(void *arg) {
  struct KernelThread *data = arg; 
  long micros = 1000000L;
  struct timespec req = {
    0,
    micros };
  struct timespec rem;

  while (data->running == 1) {
    nanosleep(&req , &rem);
    // printf("External thread wakeup...\n");
    for (int x = 0; x < data->buffers->count; x++) {
      //printf("Writing to buffer\n");
      if (data->buffers->buffer[x].available == 0) {
        data->buffers->buffer[x].data = "Hello world";
        data->buffers->buffer[x].available = 1;
      }
    }
    asm volatile ("mfence" ::: "memory");
  }
  return 0; 
}

int do_protected_write(struct BarrierTask *data) {

  struct ProtectedState *protected = data->thread->protected_state;
  data->v++; // thread local
    // printf("Protected %d %d\n", data->task_index, data->thread_index);
  protected->protected++; // shared between all threads
  if (protected->balance > 0) {
    protected->balance -= 500; // shared between all threads
  } else {
    protected->balance += 500; // shared between all threads
  }
  return 0; 
}
int sendm(struct BarrierTask *data) {
  if (data->sending == 1) {
      for (int n = 0 ; n < data->thread_count; n++) {
        if (n == data->thread_index) { continue; }
        struct Data *them = data->mailboxes[n].higher;
        // printf("Sending to thread %d\n", n);
        int min = them->messages_limit;
        //if (them->messages_limit < min) {
        //  min = them->messages_limit;
        //}
        for (; them->messages_count < min;) {
          data->n++;
          data->mailboxes[n].sent++;
          them->messages[them->messages_count++] = data->message; 
        }
        asm volatile ("sfence" ::: "memory");
      }
    } else {
    printf("not sending\n");
  }
  return 0;
}
int receive(struct BarrierTask *data) {
  // printf("Receiving\n");
  for (int n = 0 ; n < data->thread_count; n++) {
    // if (n == data->thread_index) { continue; }
    struct Data *me = data->mailboxes[n].lower;
    for (int x = 0 ; x < me->messages_count ; x++) {
      data->sends++;
      data->n++;
      data->mailboxes[n].received++;
      // printf("on %d from %d task %d received: %s\n", data->thread_index, n, data->task_index, me->messages[x]->message);
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread_index) {
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread_index);
        exit(1);
      }
    }
    me->messages_count = 0;
    asm volatile ("sfence" ::: "memory");
  }

}

int barriered_work(struct BarrierTask *data) {
  // printf("In barrier work task %d %d\n", data->thread_index, data->task_index);
  // printf("%d %d Arrived at task %d\n", data->thread->real_thread_index, data->thread_index, data->task_index);
  long *n = &data->n;
  // we are synchronized
  if (data->thread_index == data->task_index) {
      receive(data);
      void * tmp; 
      // swap this all thread's write buffer with the next task
        int t = data->task_index;
        for (int y = 0; y < data->thread_count ; y++) {
          for (int b = 0; b < data->thread_count ; b++) {
              int next_task = abs((t + 1) % (data->thread_count));
              tmp = data->thread->threads[y]->tasks[t].mailboxes[b].higher; 
              // data->thread->threads[y].tasks[t].mailboxes[b].higher = data->thread->threads[b].tasks[next_task].mailboxes[y].lower;
              data->thread->threads[b]->tasks[next_task].mailboxes[y].lower = tmp;
            }
        }
      asm volatile ("sfence" ::: "memory");
        // printf("move my %d lower to next %d lower\n",data->task_index, next_task);


    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    int modcount = ++data->thread->protected_state->modcount;

    
    while (data->scheduled == 1) {
      data->n++;
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
      asm volatile ("sfence" ::: "memory");
    } 
  
    if (modcount != data->thread->protected_state->modcount) {
      printf("Race condition!\n");
    }
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    sendm(data);
  } else {
    receive(data);
  
    
    while (data->scheduled == 1) {
      data->n++;
      asm volatile ("sfence" ::: "memory");
    }
  
    sendm(data);
  }
  asm volatile ("sfence" ::: "memory");
  return 0;
}



int barriered_work_ingest(struct BarrierTask *data) {
  // printf("Ingest task\n");
  for (int x = 0 ; x < data->thread->buffers->count ; x++) {
    // printf("Checking buffer %d\n", data->thread->buffers->buffer[x].available);
    if (data->thread->buffers->buffer[x].available == 1) {
      data->ingest_count++;
      // printf("Ingested %s\n", (char*)data->thread->buffers->buffer[x].data);
      data->thread->buffers->buffer[x].available = 0;
    } else {
    }
  }
  asm volatile ("sfence" ::: "memory");
  barriered_work(data);
  return 0;
}

int barriered_nulltask(struct BarrierTask *data) {
  // printf("In barrier null task %d %d\n", data->thread_index, data->task_index);
  return 0;
}
int barriered_steal(struct BarrierTask *data) {
  // printf("In barrier steal task %d %d\n", data->thread_index, data->task_index);
  return 0;
}
int barriered_reset(struct BarrierTask *data) {
  // printf("In barrier reset task %d %d\n", data->thread_index, data->task_index);
    for (int x = 0 ; x < data->task_count ; x++) {
      // printf("Resetting %d %d\n", data->thread_index, x);
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
      // data->thread->tasks[x].arrived++; 
      
      data->thread->tasks[x].available = 1; 
  }
  asm volatile ("sfence" ::: "memory");
  return 0;
}

int after(struct timespec left, struct timespec right) {
  return left.tv_sec > right.tv_sec &&
         left.tv_nsec > right.tv_nsec;
}

int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    return 1;
  }
  return 0;
}

int overlap(struct Snapshot left, struct Snapshot right) {

  if (after(left.start, right.start) && after(right.end, left.end)) {
    return 1;
  }
  if (after(right.start, left.start) && after(left.end, right.end)) {
    return 1;
  }
  if (within(left.start, right.start, right.end, left.end) == 1) {
    return 1;
  }
  if (within(right.start, left.start, left.end, right.end) == 1) {
    return 1;
  }
  return 0;
}

int verify(struct KernelThread *thread_data, int thread_count) {

  for (int x = 0 ; x < thread_count; x++) {
    for (int z = 0 ; z < thread_count; z++) {
      if (z != x)  {
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
          printf("Verifying thread %d\n", x);
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);

            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {

                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
                  /*
                     if (thread_data[x].tasks[y].snapshots[n].start.tv_sec <= thread_data[z].tasks[k].snapshots[m].start.tv_sec &&
                     thread_data[x].tasks[y].snapshots[n].start.tv_nsec <= thread_data[z].tasks[k].snapshots[m].start.tv_nsec &&
                     thread_data[z].tasks[k].snapshots[m].end.tv_sec >= thread_data[x].tasks[y].snapshots[n].end.tv_sec &&
                     thread_data[z].tasks[k].snapshots[m].end.tv_nsec >= thread_data[x].tasks[y].snapshots[n].end.tv_nsec) {
                   */

                  printf("Race condition %ld  %ld %ld %ld\n", thread_data[x].tasks[y].snapshots[n].start.tv_sec, thread_data[z].tasks[k].snapshots[m].end.tv_sec, thread_data[x].tasks[y].snapshots[n].start.tv_nsec, thread_data[z].tasks[k].snapshots[m].end.tv_nsec  );
                }

                } 
              }

            }
          }
        }
      } 
    }


  return 0;
}
int main() {
  int thread_count = 12;
  int timer_count = 1;
  int io_threads = 1;
  int external_threads = 1;
  int buffer_size = 1;
  long messages_limit = 1;
  int total_threads = thread_count + timer_count + io_threads + external_threads;
  printf("Multithreaded nonblocking lock free MULTIbarrier runtime (https://github.com/samsquire/assembly)\n");
  printf("\n");
  printf("Barrier runtime parameters:\n");
  printf("worker thread count = %d\n", thread_count);
  printf("total threads = %d\n", total_threads);
  printf("io threads = %d\n", io_threads);
  printf("scheduler threads = %d\n", timer_count);
  printf("external thread count = %d\n", external_threads);
  printf("external thread ingest buffer size = %d\n", buffer_size);
  printf("intrathread message buffer size = %ld\n", messages_limit);
  printf("per thread runtime %ldns\n", TICK);
  printf("duration %d seconds", DURATION);
  printf("\n\n");


  struct ProtectedState *protected_state = calloc(thread_count, sizeof(struct ProtectedState));
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 

  int barrier_count = 2;
  int total_barrier_count = barrier_count + 1;
  int timer_index = thread_count;
  int io_index = timer_index + timer_count;

  struct Buffers *buffers = calloc(external_threads, sizeof(struct Buffers));
  
  for (int x = 0 ; x < external_threads; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
    }
  }
  int external_thread_index = 0;
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  for (int x = 0 ; x < total_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    int other = -1;
    cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    CPU_ZERO(sendercpu);
    if (x % 2 == 1) {
      other = abs(x - 1) % total_threads;
      thread_data[x].thread_index = 1;
      my_thread_data[0] = &thread_data[other]; 
      my_thread_data[1] = &thread_data[x]; 
      printf("odd %d %p %p\n", x, my_thread_data[0], my_thread_data[1]);
      thread_data[x].protected_state = &protected_state[other];
    } else {
      thread_data[x].thread_index = 0;
      other = (x + 1) % total_threads;
      my_thread_data[0] = &thread_data[x]; 
      my_thread_data[1] = &thread_data[other]; 
      printf("even %d %p %p\n", x, my_thread_data[0], my_thread_data[1]);
      thread_data[x].protected_state = &protected_state[x];
    }
    printf("i am %d, other is %d my thread index is %d\n", x, other, thread_data[x].thread_index);
    thread_data[x].other = other;
    for (int j = 0 ; j < cores / 2 ; j++) {
      printf("assigning thread %d to core %d\n", x, j);
      CPU_SET(j, sendercpu);
    }
    thread_data[x].cpu_set = sendercpu;
    thread_data[x].real_thread_index = x;
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = 2;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].task_count = total_barrier_count;
    thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    thread_data[x].timestamp_count = 0;
    thread_data[x].timestamp_limit = timestamp_limit;
    thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    thread_data[x].task_timestamp_count = 0;
    thread_data[x].task_timestamp_limit = timestamp_limit;

      struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
      thread_data[x].tasks = barriers;

      for (int y = 0 ; y < total_barrier_count ; y++) {
        // if the task number is identical to the thread
        // number then we are synchronized
        /*
                      thread
              t     x
              a       x
              s         x
              k           x
        */
        thread_data[x].tasks[y].protected = do_protected_write; 
        struct Mailbox *mailboxes = calloc(thread_count, sizeof(struct Mailbox));
        thread_data[x].tasks[y].mailboxes = mailboxes;
        // long messages_limit = 20;/*9999999;*/
        for (int b = 0 ; b < 2 ; b++) {
          struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
          struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
          struct Data *data = calloc(2, sizeof(struct Data));

          mailboxes[b].lower = &data[0];
          mailboxes[b].higher = &data[1];
          data[0].messages = messages;
          data[1].messages = messages2;
          data[0].messages_limit = messages_limit;
          data[0].messages_count = 0;
          data[1].messages_count = 0;
          data[1].messages_limit = messages_limit;
        }

        char *message = malloc(sizeof(char) * 256);
        struct Message *messaged = malloc(sizeof(struct Message));
        memset(message, '\0', 256);
        sprintf(message, "Sending message from thread %d task %d", x, y);
        messaged->message = message;
        messaged->task_index = y;
        messaged->thread_index = thread_data[x].thread_index;
        thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
        thread_data[x].tasks[y].message = messaged;
        thread_data[x].tasks[y].sending = 1;
        thread_data[x].tasks[y].snapshot_count = 99;
        thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
        thread_data[x].tasks[y].current_snapshot = 0;
        thread_data[x].tasks[y].thread_index = thread_data[x].thread_index;
        thread_data[x].tasks[y].thread = &thread_data[x]; 
        thread_data[x].tasks[y].available = 1;
        thread_data[x].tasks[y].arrived = 0;
        thread_data[x].tasks[y].thread_count = 2;
        thread_data[x].tasks[y].task_count = total_barrier_count;
        thread_data[x].tasks[y].worker_count = thread_count;
        thread_data[x].tasks[y].task_index = y;
        if (y == barrier_count - 1) {
          /*
          if (x == thread_count - 1) {
            thread_data[x].tasks[y].run = barriered_steal; 
          } else {
            thread_data[x].tasks[y].run = barriered_nulltask; 
          }
          */
          thread_data[x].tasks[y].run = barriered_work; 
        } else {
          if (x == y && external_thread_index < external_threads && ((x % external_threads) == 0)) { 
            printf("Thread %d is an ingest thread\n", x);
            thread_data[x].buffers = &buffers[external_thread_index++];
            thread_data[x].tasks[y].run = barriered_work_ingest; 
          } else {
            thread_data[x].tasks[y].run = barriered_work; 

          }
        }
      }
      thread_data[x].tasks[barrier_count].protected = do_protected_write; 
      thread_data[x].tasks[barrier_count].run = barriered_reset; 
      thread_data[x].tasks[barrier_count].thread = &thread_data[x]; 
      thread_data[x].tasks[barrier_count].available = 1; 
      thread_data[x].tasks[barrier_count].arrived = 0; 
      thread_data[x].tasks[barrier_count].task_index = barrier_count; 
      thread_data[x].tasks[barrier_count].thread_count = 2; 
      thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
      thread_data[x].tasks[barrier_count].worker_count = thread_count; 
      thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
  }
  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    my_thread_data[0] = &thread_data[x]; 
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 

    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = 2;
    thread_data[x].thread_index = 0;
    thread_data[x].task_count = total_barrier_count;
  }
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));

  thread_data[thread_count].type = TIMER;
  thread_data[thread_count].running = 1;
  thread_data[thread_count].task_count = total_barrier_count;

  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
  }
  thread_data[thread_count].threads = my_thread_data;
  thread_data[thread_count].thread_count = thread_count;
  thread_data[thread_count].my_thread_count = 2;
  thread_data[thread_count].thread_index = 0;

  printf("Creating scheduler thread %d\n", thread_count);
  pthread_create(&thread[thread_count], &timer_attr[thread_count], &timer_thread, &thread_data[thread_count]);
  for (int x = 0 ; x < thread_count ; x++) {
    thread_data[x].type = WORKER;
    thread_data[x].running = 1;
    printf("Creating kernel worker thread %d\n", x);
    pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].thread_index = x;
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = &buffers[buffer_index];

    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
  }
  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    void * result; 
    pthread_join(thread[x], &result);
    printf("Finished thread %d\n", x);
  }
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
  for (int x = 0 ; x < thread_count ; x++) {
    long v = 0;
    
    int other = -1;
    int me = x;
    if (x % 2 == 1) {
      other = abs(x - 1) % total_threads;
    } else {
      other = (x + 1) % total_threads;
    }
    printf("\n");
    printf("Total Protected %ld\n", protected_state[me].protected);

    for (int n = 0 ; n < thread_data[me].task_count ; n++) {
      v += thread_data[me].tasks[n].v;
    }
    for (int n = 0 ; n < thread_data[other].task_count ; n++) {
      v += thread_data[other].tasks[n].v;
    }
    printf("Total V %ld\n", v);
    printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    printf("\n");
    for (int n = 0 ; n < thread_data[x].task_count ; n++) {
      total += thread_data[x].tasks[n].n;
      ingests += thread_data[x].tasks[n].ingest_count;
      sends += thread_data[x].tasks[n].sends;
      for (int k = 0 ; k < thread_count ; k++) {
        sents += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).sent;
        received += ((struct Mailbox)thread_data[x].tasks[n].mailboxes[k]).received;
      }
    }
    for (int n = 0 ; n < thread_data[x].timestamp_limit ; n++) {
      struct timespec start = thread_data[x].start[n];
      struct timespec end = thread_data[x].end[n];
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      // printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
      // printf("%ld iterations\n", thread_data[x].iteration_count);
    }
    for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
      struct timespec start = thread_data[x].task_snapshot[n].task_start;
      struct timespec end = thread_data[x].task_snapshot[n].task_end;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
      // printf("%ldns per thread\n", (seconds2 / 2));
    }
    // printf("cycles %ld\n", thread_data[x].cycles);
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
  printf("Total Requests per second %ld\n", total / DURATION);
  printf("Total sents %ld\n", sents / DURATION);
  printf("Total receives %ld\n", received / DURATION);
  // verify(thread_data, thread_count);
  return 0;

}
