

.PHONY: all purse abs

all: purse abs

purse: 
	caduceus purse.c
	make -f purse.makefile simplify
	make -f purse.makefile coq

abs: 
	caduceus abs.c
	make -f abs.makefile simplify
	make -f abs.makefile coq

clean:
	make -f purse.makefile clean
	make -f abs.makefile clean
	rm -f why/*.why
