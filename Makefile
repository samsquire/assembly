CC=gcc
CFLAGS=-luring -g -lm -O3
DEPS = 
CFILES=$(wildcard *.c)
OBJ=$(patsubst %.c,%,$(CFILES))
all: $(OBJ)
%: %.c 
	$(CC) -o $@ $< $(CFLAGS)
	objdump -drwC  -S $@ > output-assembly/$@.S


default: $(OBJ)
	echo $(CFILES); echo $(OBJ) \;
	$(CC) -o $@ $^ $(CFLAGS)

clean:
	rm $(OBJ)
