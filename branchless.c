#include <stdio.h>
#include <stdlib.h>
int getnum() {
    char *buffer = NULL;
    int read;
    long len = 0;
    read = getline(&buffer, &len, stdin);
    if (-1 != read)
        puts(buffer);
    else
        printf("No line read...\n");

    printf("Size read: %d\n Len: %ld\n", read, len);

    long long num = strtol(buffer, NULL, 10); 
    printf("Parsed %lld\n", num);
    free(buffer);

    return num;
}

int main(int argc, char *argv[])
{
    int num1 = getnum();
    int num2 = getnum();
    int num3 = getnum();
    long c = (num1 > 1500);
    long m = (num2 > 1600) << 1;
    long z = (num3 > 1700) << 2;

    printf("result: %ld\n",  c | m | z);

    return 0;
}

