
rev:
	caduceus reverse.c
	make -f reverse.makefile do_simplify

all: reverse has_cycle

%: %.c 
	caduceus $*.c
	make -f $*.makefile simplify
	make -f $*.makefile coq

clean:
	make -f reverse.makefile clean
	make -f has_cycle.makefile clean
	rm -f why/*.why
