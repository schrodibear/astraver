

.PHONY: all purse abs swap

all: max abs swap

%.do: %.c 
	caduceus $*.c
	make -f $*.makefile simplify
	make -f $*.makefile coq

clean:
	make -f purse.makefile clean
	make -f abs.makefile clean
	rm -f why/*.why
