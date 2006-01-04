
all: swap reverse

rev:
	caduceus reverse.c
	make -f reverse.makefile do_simplify

swap:
	caduceus swap.c
	make -f swap.makefile simplify
	make -f swap.makefile coq

%: %.c 
	caduceus $*.c
	make -f $*.makefile simplify
	make -f $*.makefile coq

clean:
	make -f reverse.makefile clean
	make -f has_cycle.makefile clean
	rm -f why/*.why
