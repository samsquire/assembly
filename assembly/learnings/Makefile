CC=gcc
CFLAGS=-lm -g
DEPS = 
CFILES=$(wildcard *.c)
DOTFILES=$(wildcard ringbuffer-tla/*.dot)
IMGS=$(patsubst %.dot,%.svg,$(DOTFILES))
OBJ=$(patsubst %.c,%,$(CFILES))
all: $(OBJ) $(IMGS)
%: %.c 
	$(CC) -o $@  $< $(CFLAGS)
	objdump -drwC  -S $@ > output-assembly/$@.S

ringbuffer-tla/%.svg: ringbuffer-tla/%.dot
	# dot -Tsvg -o $@ $<

default: $(OBJ) $(IMGS)
	echo $(CFILES); echo $(OBJ) \;
	$(CC) -o $@ $^ $(CFLAGS)

check:
	sort mailbox2 | uniq -c | sort -nr	

checkst:
	sort mailbox1 | uniq -c | sort -nr	

clean:
	rm $(OBJ)

cxx:
#	g++ multibarrier-split-io-cxx.c -o multibarrier-split-io-cxx -std=c++17 -luring -g -pg -lrocksdb -lzstd -lsnappy -llz4 -lz -lbz2 -O3 -lm -Lrocksdb/ 2> errors
	g++ tree234.c multibarrier-split-io-cxx.c -o multibarrier-split-io-cxx -std=c++17 -luring -lrocksdb -lzstd -lsnappy -llz4 -lz -lbz2 -O3 -lm -Lrocksdb/ 2> errors
	# g++ multibarrier-split-io.o rocksdb/librocksdb.a -std=c++17 -fpermissive -luring -O3 -lm -Lrocksdb/ 2>> errors
