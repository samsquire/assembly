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

#define MAILBOX_FRIEND 1
#define MAILBOX_FOREIGN 2

#define MAILBOX_LOWER 1
#define MAILBOX_HIGHER 2

#define WAITING 0
#define READY 1

struct Coroutine {
  char * pos; // %rip
  char * vars;  // local vars
  long state; // ready+notready
};

struct LoopInstance {
  
};

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
  int available __attribute__((aligned (128)));
  struct Snapshot *snapshots;
  int snapshot_limit;
  int ingest_snapshot;
};

struct Request {
    int event_type;
    int iovec_count;
    int client_socket;
    struct iovec iov[];
};

struct Mailbox {
  void *lower __attribute__((aligned (128)));
  void *higher __attribute__((aligned (128)));
  void *pending_lower;
  void *pending_higher;
  void ** stack;
  void *my_lower;
  void *my_higher;
  int kind;
  int other;
};

struct Data {
  struct Message **messages;
  long messages_count __attribute__((aligned (128)));
  long messages_limit;
  int available_sending __attribute__((aligned (128)));
  int available_receiving __attribute__((aligned (128)));
  int available_reading __attribute__((aligned (128)));
  int available_swapping __attribute__((aligned (128)));
  int finished_reading __attribute__((aligned (128)));
  long sent __attribute__((aligned (128)));
  long received __attribute__((aligned (128)));

  int kind;
  int a;
  int b;
  int c;
  int id;
};

struct Message {
  char * message;
  long thread_index;
  long task_index;
  int group;
};

#define BARRIER_TASK 65
struct BarrierTask {
  int kind;
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
  int total_thread_count;
  int all_thread_count;
  int mailbox_thread_count;
  int available;
  int task_count;
  int scheduled;
  struct Snapshot *snapshots;
  long snapshot_count;
  long current_snapshot;
  long ingest_count;
  struct Mailbox *mailboxes;
  long sends __attribute__((aligned (128)));
  int sending;
  int worker_count;
  struct Message *message;
  int next_thread;
  int group;
  int swap;
  int wait;
};
struct TaskSnapshot {
  struct timespec task_start ;
  struct timespec task_end ;
  int task;
};

struct Group {
  int arrived __attribute__((aligned (128))); 
  int prearrive __attribute__((aligned (128))); 
  struct KernelThread **threads;
  int thread_count;
  struct Global *global;
  int seq;
};

struct Global {
  int request_group_sync;
};

#define KERNEL_THREAD 95
struct KernelThread {
  int kind;
  int thread_index;
  int real_thread_index;
  int type; 
  int preempt_interval;
  struct KernelThread **threads;
  struct KernelThread *all_threads;
  int thread_count;
  int total_thread_count;
  int my_thread_count;
  struct BarrierTask *tasks;
  int task_count;
  int running;
  struct ProtectedState *protected_state;
  struct Buffers **buffers;
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
	int buffers_count;
  int group_count;
  int threads_per_group;
  pthread_mutex_t *swapmutex;
  pthread_mutex_t *mswapmutex;
  struct Group * group_data;
  struct Group ** all_groups;
  int group;
  struct Global * global;
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

int minf(int a, int b) {
  if (a < b) { return a; }
  if (b < a) { return b; }
  return a;
}
int maxf(int a, int b) {
  if (a > b) { return a; }
  if (b > a) { return b; }
  return a;
}

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
        strcat(final_path, path);    }

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

int barriered_work_ingest(struct BarrierTask *data) {
  // printf("Ingest task %d\n", data->kind);
  // printf("Thread kind %d\n", data->thread->kind);
  int ingested = 0;
  // printf("ingest %d\n", data->thread->buffers_count);
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
      // printf("Checking buffer %d\n", data->thread->buffers->buffer[x].available);
      if (data->thread->buffers[b]->buffer[x].available == 1) {
        data->ingest_count++;
        // printf("Ingested %s\n", (char*)data->thread->buffers->buffer[x].data);
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
        data->thread->buffers[b]->buffer[x].available = 0;
        ingested++;
        asm volatile ("sfence" ::: "memory");
      } else {
      }
    }
  }
  // printf("Received %d items\n", ingested);
  // barriered_work(data);
  return 0;
}
int receive(struct BarrierTask *data) {
  // printf("Receiving\n");
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    if (n == data->thread->real_thread_index) { continue; }

    struct Data *me = data->mailboxes[n].lower;
    if (me->available_reading == 1) {
      // printf("Foreign mailbox %d is available for receiving\n", n);
    } 
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
      // printf("Foreign mailbox %d is NOT available for receiving\n", n);
      continue;
    }
    // printf("startreceive %d %d\n", n, data->thread->real_thread_index); 
    int min = me->messages_limit;
    for (; me->messages_count > 0 ; ) {
      int x = me->messages_count - 1;
      me->messages_count--;
      data->sends++;
      data->n++;
      me->received++;
      // printf("%d Received %s\n", data->thread_index, me->messages[x]->message);
      // printf("on %d from %d task %d received: %s\n", data->thread_index, n, data->task_index, me->messages[x]->message);
      if (me->messages[x]->group == data->group) {
        // printf("Received a friend message\n");
      }
      if (me->messages[x]->group != data->group) {
        // printf("Received a foreign message\n");
      }
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
        exit(1);
      }
    }
    // me->messages_count = 0;
      // mailbox is available for sending again
      me->available_reading = 0;
      me->finished_reading = 1;
      me->available_sending = 1;
  // printf("endreceive %d %d\n", n, data->thread->real_thread_index); 
  }
  asm volatile ("sfence" ::: "memory");
}

int sendm(struct BarrierTask *data) {
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
        if (n == data->thread->real_thread_index) { continue; }

        
        struct Data *them = data->mailboxes[n].higher;
        if (them->messages_count > 0) {
          // printf("there's unprocessed messages in this mailbox!\n");
          continue;
        } 
        if (them->available_sending == 1) {
          // printf("Foreign mailbox %d is available for sending\n", n);
        } 
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
          // printf("Foreign mailbox is NOT available for sending\n");
          continue;
        }
        // printf("Sending to thread %d\n", n);
        int min = them->messages_limit;
        //if (them->messages_limit < min) {
        //  min = them->messages_limit;
        //}
        if (data->sending == 1) {
          for (; them->messages_count < min;) {
            data->n++;
            them->sent++;
            them->messages[them->messages_count++] = data->message; 
          }
        
          // available for reading by external thread
          them->available_sending = 0;
          them->available_reading = 1;
          // them->available_swapping = 1;
          them->available_receiving = 1;
        }
      }
      asm volatile ("sfence" ::: "memory");
  return 0;
}

struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
  if (kind == 0) {
    // printf("getting lower\n");
    return mailbox->lower;
  }
  else if (kind == 1) {
    // printf("getting higher\n");
    return mailbox->higher;
  }
  return NULL;
}

int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
  if (kind == 0) {
    mailbox->lower = data;
  }
  if (kind == 1) {
    mailbox->higher = data;
  }
  if (kind == 2) {
    mailbox->pending_lower = data;
  }
  if (kind == 3) {
    mailbox->pending_higher = data;
  }
  return 0;
}

int fswap(struct BarrierTask *data) {

  int t = data->task_index;
    int k = data->group;

      int y = (k * data->thread->threads_per_group) + data->thread_index;
      // printf("checking y%d\n", y); 
      int g = data->group;
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
        
        int b = (g * data->thread->threads_per_group) + m;

        // printf("y = %d b = %d\n", y, b);
        // printf("from %d to %d\n", data->all_thread_count, data->mailbox_thread_count);
        int next_task = abs((t + 1) % (data->thread_count));
        int previous_task = abs((t - 1) % (data->thread_count));
        // printf("thread count %d\n", data->thread_count);
        /*printf("%d -> %d %d %d\n", y, b, t, next_task);
        printf("pointer %p\n", &data->thread->all_threads[y]);
        printf("pointer2 %p\n", data->thread->all_threads[y].tasks);
        printf("pointer3 %p\n", &data->thread->all_threads[y].tasks[t]);
        printf("pointer4 %p\n", &data->thread->all_threads[y].tasks[t].mailboxes);
        printf("pointer5 %p\n", &data->thread->all_threads[y].tasks[t].mailboxes[b]);
        */
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
        // printf("kind %d\n", kind);
        if (kind == MAILBOX_FRIEND) {
           // printf("friend %d/%d with %d/%d\n", y, t, b, next_task);
          // printf("Mailbox is a friend\n");
          // data->thread->all_threads[y].tasks[t].mailboxes[b].higher = data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower;
            int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
            // printf("I am %d they are %d\n", b, other);
            int otherkind = data->thread->all_threads[other].tasks[next_task].mailboxes[y].kind; 
            // printf("otherkind is %d\n", otherkind);

            
            // fswap
             for (int nn = 0 ; nn < data->thread_count; nn++) {
              int next_task = abs((nn + 1) % (data->thread_count));
              int LOWER = 0; int HIGHER = 1; int PENDING = 2;
              int l1 = 0;
              int l2 = b;
              int l3 = nn;
              int l4 = y;
              struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
              struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
                if (source2->messages_count != 0) { 
                  break;
                }

              struct Mailbox* __a = &data->thread->all_threads[l2].tasks[l3].mailboxes[l4];
              // printf("%d bef\n", ((struct Data*)__a->higher)->id); 
              int t1 = 1;
              int t2 = y;
              int t3 = next_task;
              int t4 = b;
              struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
                if (dest->messages_count != 0) { 
                  continue;
                }
              struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
              // source higher to dest lower for reading
              setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source, LOWER);
              // need to replace lower of source with dest
              setmailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], dest2, LOWER);

              setmailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], dest, HIGHER);
              setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source2, HIGHER);
              /*
              ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
              ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
              ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].higher)->available_sending = 1;

              ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_sending = 1;
              */
              // printf("swapped riend %d\n", data->thread->real_thread_index);
              // printf("%d aft\n", ((struct Data*)__a->lower)->id); 
            }
            // break;
            // printf("datakind1 %d %p\n", data->kind, data->thread);
            // printf("lower %p\n", data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower);
            // data->thread->all_threads[y].tasks[t].mailboxes[b].higher = data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower;
            // printf("swapping %d/%d with %d/%d\n", y, t, b, next_task);
            // printf("swapped friend\n");
      
        } else {
            }
            // printf("Mailbox is external, swapped\n");

        
        // data->thread->threads[y].tasks[t].mailboxes[b].higher = data->thread->threads[b].tasks[next_task].mailboxes[y].lower;
            
   }
  return 0;
}

int barriered_work(struct BarrierTask *data) {
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    // printf("%d %d\n", data->thread->group_data->arrived, data->thread->group_data->seq);
    // printf("%d\n", data->arrived);
    if (data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
      // printf("%d Starting group sync from %d\n", data->thread->group, data->thread->global->request_group_sync);
      data->thread->global->request_group_sync = (data->thread->group + 1) % data->thread->group_count;
    } else
    if (data->thread->global->request_group_sync != -1) {
      data->thread->global->request_group_sync = (data->thread->group + 1) % data->thread->group_count;
      
      // printf("%d In group sync from %d\n", data->thread->group, data->thread->global->request_group_sync);
    }
    // printf("In barrier work task %d %d\n", data->thread_index, data->task_index);
    // printf("%d %d Arrived at task %d\n", data->thread->real_thread_index, data->thread_index, data->task_index);
    long *n = &data->n;
          int t = data->task_index;
    // we are synchronized within a group
    if (data->thread_index == data->task_index) {
      receive(data);
    // printf("Thread is %d\n", data->thread->real_thread_index);
        void * tmp; 
        // swap this all thread's write buffer with the next task
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
                int next_task = abs((t + 1) % (data->thread_count));
                int previous_task = abs((t - 1) % (data->thread_count));
          int b = data->thread->real_thread_index;
                if (y == b) { continue; }
                     // printf("is available\n"); 
                   //printf("rti %d %d", y, data->thread->real_thread_index);
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
                      // the other thread has finished writing to our mailbox
  // them->available_sending
                    // printf("%d: we are %d and they are %d\n", data->thread->real_thread_index, b, y);

                        // printf("We own thread %d and thread %d has finished writing to us \n", data->thread->real_thread_index, y);
                        /*
                        */
                        // ((struct Data*)data->thread->all_threads[y].tasks[next_task].mailboxes[b].higher)->available_receiving = 0;

    
                        // there can only be one mailbox per thread-pair
                        // this is why this didn't work before
                        
                        /*
                        */
                        // we read other threads writings to us
                    // in thread-1
                    // y=1 b =2 and b=3
                    // in thread 3
                    // y=3 b=0 b=1

                    // b=5 y=3
                    // b=3 y=5
                    //mmswap
                      int min = minf(b, y); 
                      int max = maxf(b, y); 
                      
                      int lookup = min + max;
                
                      // printf("lookup %d %d %d\n", lookup, b, y); 
                      for (int nn = 0; nn < data->thread_count; nn++) {
                        int next_task = abs((nn + 1) % data->thread_count);
                        // printf("%d to %d\n", nn, next_task);
                        int LOWER = 0; int HIGHER = 1;
                        // b=5 y=3
                        // b=3 y=5
                        int l1 = 0;
                        int l2 = b;
                        int l3 = nn;
                        int l4 = y;
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
                        struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);
                        struct Mailbox* __a = &data->thread->all_threads[l2].tasks[l3].mailboxes[l4];
                        // printf("%d bef\n", ((struct Data*)__a->higher)->id); 
                        // y=5 b=3
                        // y=3 b=5
                        int t1 = 1;
                        int t2 = y;
                        int t3 = next_task;
                        int t4 = b;
                        struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
                        struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
                        // source higher to dest lower for reading
      
                        // need to replace lower of source with dest
                          setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source, LOWER);
                          setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source2, HIGHER);
                          setmailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], dest2, LOWER);
                          setmailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], dest, HIGHER);

                        for (int jj = 0 ; jj < data->thread_count; jj++) {
                          data->thread->all_threads[l2].tasks[jj].swap = 1;
                          data->thread->all_threads[t2].tasks[jj].swap = 1;
                        }
                        // printf("%d aft\n", ((struct Data*)__a->lower)->id); 
                            // printf("%p\n", ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher));
                            // printf("%d\n", ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading);
                             // ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
                             // ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
                             ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
                             ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;

                            ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
                            ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;

                            // ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_sending = 1;
                            // ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].higher)->available_sending = 1;
                      
                      } 
                      /* 
                      for (int nn = 0; nn < data->thread_count; nn++) {
                        int next_task = abs((nn + 1) % data->thread_count);
                        // printf("%d to %d\n", nn, next_task);
                        int LOWER = 0; int HIGHER = 1; int PENDING = 2;
                        // b=5 y=3
                        // b=3 y=5
                        int l1 = 0;
                        int l2 = y;
                        int l3 = nn;
                        int l4 = b;
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
                        struct Data* source2 = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], LOWER);

                        struct Mailbox* __a = &data->thread->all_threads[l2].tasks[l3].mailboxes[l4];
                        // printf("%d bef\n", ((struct Data*)__a->higher)->id); 
                        // y=5 b=3
                        // y=3 b=5
                        int t1 = 1;
                        int t2 = b;
                        int t3 = next_task;
                        int t4 = y;
                        struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
                        struct Data *dest2 = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], HIGHER);
                        // source higher to dest lower for reading
                        setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source, LOWER);
      
                        // need to replace lower of source with dest
                        setmailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], dest2, LOWER);

                        setmailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], dest, HIGHER);
                        setmailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], source2, HIGHER);
                        // printf("%d aft\n", ((struct Data*)__a->lower)->id); 
                            // printf("%p\n", ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher));
                            // printf("%d\n", ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading);
                             ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
                             ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
                             ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
                             ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;

                            ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
                            ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;

                            // ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_sending = 1;
                            // ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].higher)->available_sending = 1;
                      
                      }  */
                        /*
                        printf("afterswap aswap\n"); 
                        printf("AfterSwapend\n");*/
                        for (int nn = 0; nn < data->thread_count; nn++) {
                          /*
                          ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].higher)->available_reading = 0;
                          ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_reading = 0;

                          ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].lower)->available_reading = 1;
                          ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].lower)->available_reading = 1;

                          ((struct Data*) data->thread->all_threads[b].tasks[nn].mailboxes[y].higher)->available_sending = 1;
                          ((struct Data*) data->thread->all_threads[y].tasks[nn].mailboxes[b].higher)->available_sending = 1;
                          */
                          if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
                            printf("Can't have the same buffer");
                            exit(1);
                          }
                        }
                        for (int nn = 0; nn < data->thread_count; nn++) {
                          // data->thread->all_threads[y].tasks[next_task].mailboxes[b].higher = _b;
                        }

                        // data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower = c;
    
   

                        // ((struct Data*)data->thread->all_threads[y].tasks[t].mailboxes[b].higher)->available_sending = 1;
                        // ((struct Data*)data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available_sending = 1;
                        
                        // other thread references read to our mailbox
                        // data->thread->all_threads[y].tasks[next_task].mailboxes[b].lower = data->thread->all_threads[b].tasks[next_task].mailboxes[y].stack[1];

                        // other thread write end to us
                        for (int nn = 0 ; nn < data->thread_count ; nn++) {
                          // data->thread->all_threads[y].tasks[nn].mailboxes[b].higher = data->thread->all_threads[y].tasks[nn].mailboxes[b].stack[0];
                        }
                        //  ((struct Data*)data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower)->available_swapping = 0;
                        // ((struct Data*)data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower)->available_receiving = 1;

                        // [lower, higher] 

                        // data->thread->all_threads[b].tasks[next_task].mailboxes[y].stack[0] = right2;
                        // data->thread->all_threads[b].tasks[next_task].mailboxes[y].stack[1] = left2;
                        
                        // ((struct Data*)data->thread->all_threads[b].tasks[next_task].mailboxes[y].higher)->available_sending = 1;



                        // printf("datakind1 %d %p\n", data->kind, data->thread);
                        // printf("lower %p\n", data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower);
                        // data->thread->all_threads[y].tasks[t].mailboxes[b].higher = data->thread->all_threads[b].tasks[next_task].mailboxes[y].lower;
                        // printf("swapping %d/%d with %d/%d\n", y, t, b, next_task);

                        // data->thread->all_threads[y].tasks[t].mailboxes[b].higher = _d;

                        // they read from what we wrote to them
                        // data->thread->all_threads[y].tasks[next_task].mailboxes[b].lower = data->thread->all_threads[b].tasks[t].mailboxes[y].higher;

                        // ((struct Data*) _f)->available_receiving = 1;
                        // data->thread->all_threads[y].tasks[t].mailboxes[b].lower = _c;

                        // we tell them to write somewhere else
                        // data->thread->all_threads[y].tasks[next_task].mailboxes[b].higher = _b;


                        // ((struct Data*)_b)->available_receiving = 1;
                        // ((struct Data*)_e)->available_sending = 1;
                        // ((struct Data*)_c)->available = 1;
                        // ((struct Data*)_d)->available = 1;
              
            }

          }
        
        fswap(data); 
        
        // mboxinner 
        /*
        struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
        int datas2_size = 0; 
        for (int k = 0 ; k < data->thread->group_count ; k++) {
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
            int x = (k * data->thread->threads_per_group) + d;
            for (int n = 0 ; n < data->thread->all_threads[x].task_count ; n++) {
              for (int kk = 0 ; kk < data->mailbox_thread_count ; kk++) {
                datas[datas2_size++] = ((struct Data*) ((struct Mailbox)data->thread->all_threads[x].tasks[n].mailboxes[kk]).lower);
                datas[datas2_size++] = ((struct Data*) ((struct Mailbox)data->thread->all_threads[x].tasks[n].mailboxes[kk]).higher);
              }
            }
          }
        }
        // printf("Mailboxes list 2 mlist2\n");
        FILE *m2;
        char * name = calloc(100, sizeof(char));
        sprintf(name, "mailbox2-%d", data->thread->real_thread_index);
        m2 = fopen(name, "w");
        for (int x = 0 ; x < datas2_size; x++) {
          char * c = calloc(250, sizeof(char));
          sprintf(c, "mailbox %d\n", datas[x]->id);
          // printf("%s", c);
          fprintf(m2, "%s", c);
        } 
        fclose(m2);
        free(datas);
        */ 

        receive(data);
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
      // sendm(data);
    } else {
      receive(data);
      
      while (data->scheduled == 1) {
        data->n++;
        asm volatile ("sfence" ::: "memory");
      }
      sendm(data);
    }
    if (t == data->thread_count - 1) {
        for (int tt = 0 ; tt < data->task_count ; tt++) {
          data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
        }
    }
    data->swap = 0;
    asm volatile ("sfence" ::: "memory");
    
    return 0;
    } else {
    // printf("Thread safe group\n");
  }
  return 0;
}

int barriered_work_ingest_andwork(struct BarrierTask *data) {
  barriered_work_ingest(data);
  barriered_work(data);
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
        int grouparrived = 0;
        int groupprearrived = 0;
        for (int thread = 0 ; thread < data->thread_count; thread++) {
          // printf("thread %d does %d %d %d == %d\n", data->thread_index, t, previous, data->threads[thread]->tasks[previous].arrived, data->tasks[t].arrived);
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
            arrived++;
          } 
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
            prearrive++;
          }
        }
        /*
        for (int gt = 0; gt < data->group_count ; gt++) { 
          if (gt == data->group) { continue; }
          int previous = gt;
          if (t > 0) {
            previous = gt - 1;
          } else {
            previous = data->group_count - 1;
          }
            // printf("%d %d\n", data->all_groups[gt]->arrived, data->all_groups[data->group]->arrived);
            if (data->all_groups[gt]->arrived == data->all_groups[data->group]->arrived) {
              grouparrived++;
            } 
            if (data->all_groups[gt]->prearrive == data->all_groups[data->group]->prearrive) {
              groupprearrived++;
            }
        }
        */
        // printf("%d %d\n", grouparrived, groupprearrived);
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
          // printf("In barrier task %d\n", data->thread_index);
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
          break;
        }   
      } else {
          // printf("%d not available\n", t);
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
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
    for (int x = 0 ; x < data->my_thread_count ; x++) {
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
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
  for (int x = 0 ; x < data->my_thread_count ; x++) {
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
      for (int y = 0 ; y < 2 ; y++) {
        for (int k = 0 ; k < data->my_thread_count; k++) {
          if (x == k) { continue; }
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
            all_empty = 0;
            struct Data* lower = ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower);
            struct Data* higher = ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher);
            printf("%d %d %d %ld %ld left %d %d\n", x, y, k, lower->messages_count, higher->messages_count, lower->id, higher->id);
            // printf("Someone unfinished\n");
            break;
          }
        }
      }
    }
    int all_waited = 1;
    int arrived = 0;
    for (int k = 0 ; k < data->my_thread_count; k++) {
      for (int tt = 0 ; tt < 2; tt++) {
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
          printf("%d\n", data->threads[k]->tasks[tt].wait);
          all_waited = 0; 
        }
      }
    }
    if (all_empty == 1 && all_waited == 1) {
      drained = 1;
    } else {
      nanosleep(&drain , &drainrem);
    }
  }
  
  printf("Finished\n");
  while (data->running) {
    // nanosleep(&req , &rem);
    for (int x = 0 ; x < data->total_thread_count ; x++) {
      printf("Checking for io thread %d\n", x);
      data->threads[x]->running = 0;
      if (data->threads[x]->type == IO) {
        printf("Stopping io_uring\n");
        eventfd_write(data->threads[x]->_eventfd, 1);
      }
    }
    // forcefully deschedule all tasks
    for (int x = 0 ; x < data->my_thread_count ; x++) {
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
    // nanosleep(&req , &rem);
    int created = 0;
    // printf("External thread wakeup...\n");
    for (int b = 0; b < data->buffers_count; b++) {
      for (int x = 0; x < data->buffers[b]->count; x++) {
	//printf("Writing to buffer\n");
				if (data->buffers[b]->buffer[x].available == 0) {
					data->buffers[b]->buffer[x].data = "Hello world";
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
					data->buffers[b]->buffer[x].available = 1;
          asm volatile ("sfence" ::: "memory");
					created++;
				}
     }
    }
    // printf("Created %d items\n", created);
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
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    data->thread->group_data->arrived++;
    // printf("Finished group %d\n", data->thread->global->request_group_sync); 
    data->thread->global->request_group_sync = -1;
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
  int core_count = 1;
  int threads_per_group = 2;
  int group_count = 3;
  int thread_count = 2;
  int mailboxes_needed = group_count * thread_count;
  int timer_count = 1;
  int io_threads = 1;
  int external_threads = 2;
  int buffer_size = 1;
  long messages_limit = 1;
  int buffers_per_thread = 1;
  int total_threads = (group_count * threads_per_group) + timer_count + io_threads + external_threads;
  printf("Multithreaded nonblocking lock free MULTIbarrier runtime (https://github.com/samsquire/assembly)\n");
  printf("\n");
  printf("Cores count %d\n", core_count);
  printf("Mailboxes needed %d\n", mailboxes_needed);
  printf("Group count %d\n", group_count);
  printf("Threads per group %d\n", threads_per_group);
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

  int dataid = 0;

  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  int cc = 0; 
  for (int x = 0 ; x < total_threads; x++) {
    for (int y = 0 ; y < total_threads; y++) {
      printf("c %d x %d y %d\n", cc, x, y);
      pthread_mutex_init(&swapmutex[cc++], NULL);
    }
  }

  int barrier_count = 2;
  int total_barrier_count = barrier_count + 1;
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    }
  }
  int external_thread_index = 0;
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
  int swap = 0;
  int groupcount = 0;
  int seq = 0;
  int seqs[] = {1, 3, 6};
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
  struct Global *global = calloc(1, sizeof(struct Global));
  global->request_group_sync = -1;
  for (int k = 0 ; k < group_count ; k++) {
    struct Group * group_data = calloc(1, sizeof(struct Group));
    struct KernelThread ** group_threads = calloc(100, sizeof(struct KernelThread*));
    all_groups[groupcount++] = group_data;
    group_data->thread_count = threads_per_group * group_count;
    group_data->threads = group_threads;
    group_data->global = global;
    group_data->seq = seqs[seq++ % 3];
    int group_thread_count = 0;
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      thread_data[x].group_data = group_data;
      thread_data[x].all_groups = all_groups;
      thread_data[x].group = k;
      thread_data[x].global = global;
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
      
      group_data->threads[group_thread_count++] = &thread_data[x];  

      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
        other = abs(x - 1) % total_threads;
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
        my_thread_data[1] = &thread_data[x]; 
        me_thread = 1;
        // printf("odd %d %p %p\n", x, my_thread_data[0], my_thread_data[1]);
        thread_data[x].protected_state = &protected_state[k];
      } else {
        thread_data[x].thread_index = 0;
        other = (x + 1) % total_threads;
        my_thread_data[0] = &thread_data[x]; 
        me_thread = 0;
        my_thread_data[1] = &thread_data[other]; 
        // printf("even %d %p %p\n", x, my_thread_data[0], my_thread_data[1]);
        thread_data[x].protected_state = &protected_state[k];
      }
      printf("i am %d, other is %d my thread index is %d\n", x, other, thread_data[x].thread_index);
      thread_data[x].other = other;
      // for (int j = 0 ; j < cores ; j++) {
        printf("assigning thread %d to core %d\n", x, curcpu);
        if (x < thread_count) {
          CPU_SET(curcpu, sendercpu);
          curcpu += 2;
        } else {
          for (int j = 0 ; j < cores ; j++) {
            CPU_SET(j, sendercpu);
          }
        }
        
      // }
      // setthread
      thread_data[x].swapmutex = swapmutex;
      thread_data[x].mswapmutex = mswapmutex;
      thread_data[x].kind = KERNEL_THREAD;
      thread_data[x].cpu_set = sendercpu;
      thread_data[x].real_thread_index = x;
      thread_data[x].threads = my_thread_data;
      thread_data[x].all_threads = thread_data;
      thread_data[x].thread_count = 2;
      thread_data[x].group_count = group_count;
      thread_data[x].threads_per_group = threads_per_group;
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
        int assigned = 0;
        // external_thread_index = 0;
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
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
          thread_data[x].tasks[y].mailboxes = mailboxes;
          // long messages_limit = 20;/*9999999;*/
          
          // mailbox-create
          for (int b = 0 ; b < mailboxes_needed ; b++) {
            // k is group
            int group_of = b / threads_per_group;
            printf("group of %d %d\n", b, group_of);
            if (k == group_of) {
              // printf("Creating friend mailbox %d\n", b);
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
              struct Data *data = calloc(3, sizeof(struct Data));

              data[0].kind = MAILBOX_LOWER;
              data[0].a = x;
              data[0].b = y;
              data[0].c = b;
              data[0].id = dataid++;

              data[1].kind = MAILBOX_HIGHER;
              data[1].a = x;
              data[1].b = y;
              data[1].c = b;
              data[1].id = dataid++;

              mailboxes[b].lower = &data[0];
              mailboxes[b].higher = &data[1];
              mailboxes[b].pending_lower = NULL;
              mailboxes[b].pending_higher = NULL;
              data[0].finished_reading = 1;
              data[1].finished_reading = 1;
              mailboxes[b].kind = MAILBOX_FRIEND;
              if (x % 2 == 0) { 
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
              } else {
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
              }
              printf("Creating friend mailbox %d other is %d\n", b, mailboxes[b].other);
              data[0].messages = messages;
              data[1].messages = messages2;
              data[0].messages_limit = messages_limit;
              data[0].messages_count = 0;
              data[1].messages_count = 0;
              data[1].messages_limit = messages_limit;

            }
          }
          for (int b = 0 ; b < mailboxes_needed ; b++) {
            int group_of = b / threads_per_group;
            if (k == group_of) {
              continue; 
            }
            printf("Creating external mailbox %d\n", b);
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
            struct Data *data = calloc(3, sizeof(struct Data));
            struct Data **stack = calloc(3, sizeof(struct Data));

            data[0].kind = MAILBOX_LOWER;
            data[0].a = x;
            data[0].b = y;
            data[0].c = b;
            data[0].id = dataid++;

            data[1].kind = MAILBOX_HIGHER;
            data[1].a = x;
            data[1].b = y;
            data[1].c = b;
            data[1].id = dataid++;

            mailboxes[b].lower = &data[0];
            mailboxes[b].my_lower = &data[0];
            mailboxes[b].higher = &data[1];
            mailboxes[b].pending_lower = NULL;
            mailboxes[b].pending_higher = NULL;
            data[0].finished_reading = 1;
            data[1].finished_reading = 1;
            mailboxes[b].my_higher = &data[1];
            mailboxes[b].kind = MAILBOX_FOREIGN;

            stack[0] = mailboxes[b].lower;
            stack[1] = mailboxes[b].higher;
            mailboxes[b].stack = (void**)stack;

            data[0].available_sending = 0;
            data[0].available_receiving = 0;
            data[0].messages = messages;
            data[1].messages = messages2;
            data[1].available_sending = 1;
            data[1].available_receiving = 0;
            data[0].messages_limit = messages_limit;
            data[0].messages_count = 0;
            data[1].messages_count = 0;
            data[1].messages_limit = messages_limit;
          }

          char *message = malloc(sizeof(char) * 256);
          struct Message *messaged = malloc(sizeof(struct Message));
          memset(message, '\0', 256);
          sprintf(message, "Sending message from thread %d task %d group %d", x, y, k);
          messaged->message = message;
          messaged->task_index = y;
          messaged->group = k;
          messaged->thread_index = thread_data[x].real_thread_index;
          // taskset
          thread_data[x].tasks[y].swap = swap;
          swap += 1;
          thread_data[x].tasks[y].group = k;
          thread_data[x].tasks[y].kind = BARRIER_TASK;
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
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
            if (y == 0) {
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
        thread_data[x].tasks[barrier_count].thread_count = 2; 
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
  int datas_size = 0; 
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
        }
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
  for (int x = 0 ; x < datas_size; x++) {
    char * c = calloc(250, sizeof(char));
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
          char * mailbox_kind = calloc(100, sizeof(char));
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
          // thread_data[x].tasks[y].mailboxes = mailboxes;
        }
      }
    }
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


  int timer_threadi = group_count * thread_count;
  thread_data[timer_threadi].type = TIMER;
  thread_data[timer_threadi].running = 1;
  thread_data[timer_threadi].task_count = total_barrier_count;




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
  }
  thread_data[timer_threadi].threads = my_thread_data;
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
  thread_data[timer_threadi].thread_index = 0;

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
      thread_data[x].running = 1;
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    }
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
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
		thread_data[x].buffers[0] = &buffers[next_buffer++];
	  thread_data[x].buffers_count = 1;
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

  for (int x = 0 ; x < total_threads ; x++) {
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    void * result; 
    pthread_join(thread[x], &result);
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
  int datas2_size = 0; 
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
        }
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
  for (int x = 0 ; x < datas2_size; x++) {
    char * c = calloc(250, sizeof(char));
    sprintf(c, "mailbox %d\n", datas[x]->id);
    printf("%s", c);
    fprintf(m2, "%s", c);
  } 
  fclose(m2);
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
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
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          printf("combo %d %d %d\n", x, n, kk);
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;

          long tempsent = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
          printf("ttotal td%d tsk%d %dmb %ld %ld\n", x, n, kk, tempsent, temprec);
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

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);

    }
        }
      }
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
  printf("Total Requests per second %ld\n", total / DURATION);
  long sentdur = sents / DURATION;
  printf("Total sents per second %ld\n", sentdur);
  long recdur = received / DURATION;
  printf("Total receives per second %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
  return 0;

}
