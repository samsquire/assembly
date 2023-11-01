CC=gcc
CFLAGS=-O3 -luring
DEPS = 
CFILES=$(wildcard *.c)
OBJ=$(patsubst %.c,%,$(CFILES))
all: $(OBJ)
%: %.c 
	$(CC) -o $@ $< $(CFLAGS)

default: $(OBJ)
	echo $(CFILES); echo $(OBJ) \;
	$(CC) -o $@ $^ $(CFLAGS)

clean:
	rm $(OBJ)