#include <stdlib.h>
#include <stdio.h>

int do_something(int ** num) {
  printf("%p\n", num);
}

int main() {
  int * num = calloc(1, sizeof(int));
  do_something(&num);
}
