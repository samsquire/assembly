.PHONY: run
SHELL := /bin/bash
CC=gcc
CFLAGS=-lm -O3 -g -luring
DEPS = 
CFILES=$(wildcard *.c)
DOTFILES=$(wildcard ringbuffer-tla/*.dot)
DIAGRAMS=$(wildcard diagrams/*.dot)
IMGS=$(patsubst %.dot,%.svg,$(DOTFILES))
DIAGRAMIMGS=$(patsubst diagrams/%.dot,diagramspng/%.png,$(DIAGRAMS))
OBJ=$(patsubst %.c,%,$(CFILES))

all: $(DIAGRAMIMGS) $(IMGS)
%: %.c 
	$(CC) -o $@  $< $(CFLAGS)
	objdump -drwC  -S $@ > output-assembly/$@.S

ringbuffer-tla/%.svg: ringbuffer-tla/%.dot
	 #dot -Tsvg -o $@ $<

diagramspng/%.png: diagrams/%.dot
	dot -Tpng -o $@ $<


#default: $(DIAGRAMIMGS) $(OBJ) $(IMGS) 
default: $(DIAGRAMIMGS) $(IMGS) 
	echo $(CFILES); echo $(OBJ) \;
	#$(CC) -o $@ $^ $(CFLAGS)

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

run:
	( cd assembly/learnings && make pthread; ) ; \
	( cd assembly; make coroutinesdirect && ./coroutinesdirect ; )