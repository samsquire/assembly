#include <stdio.h>
#include <stdlib.h>

int main() {
    double* p = calloc(1, sizeof(double));
    *p = 6;
    printf("Hi world %f", *p);
}
