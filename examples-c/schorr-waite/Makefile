
all: schorr_waite

%: %.c 
	caduceus $*.c
	make -f $*.makefile simplify
	make -f $*.makefile coq

clean:
	make -f schorr_waite.makefile clean
	rm -f why/*.why
