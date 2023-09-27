#include <stdlib.h>

struct Task {
  int one;
};

int main(int argc, char argv[]) {
  struct Task * task = malloc(sizeof(struct Task));
  free(task);
  return 0;
}
