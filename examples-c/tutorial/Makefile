

all: max abs swap purse

%: %.c 
	caduceus $*.c
	make -f $*.makefile simplify
	make -f $*.makefile coq

clean:
	make -f purse.makefile clean
	make -f abs.makefile clean
	rm -f why/*.why
