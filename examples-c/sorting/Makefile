
all: selection

%: %.c 
	caduceus $*.c
	#	make -f $*.makefile simplify
	make -f $*.makefile coq

clean:
	make -f selection.makefile clean
	rm -f why/*.why
