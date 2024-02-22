CC=gcc
CFLAGS=-luring -lm -O3
DEPS = 
CFILES=$(wildcard *.c)
DOTFILES=$(wildcard ringbuffer-tla/*.dot)
IMGS=$(patsubst %.dot,%.svg,$(DOTFILES))
OBJ=$(patsubst %.c,%,$(CFILES))
all: $(OBJ) $(IMGS)
%: %.c 
	$(CC) -o $@ $< $(CFLAGS)
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
