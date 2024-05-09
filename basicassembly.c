#include <stdio.h>
int main(int argc, char **argv) {
  int run = 1;
  while (argc == 6) {
    printf("loop\n");
    if (argv == 27) {
      run = 0;
    }
    argc++;
  }
  return 0;
}