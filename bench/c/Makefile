CADUCEUS=../../bin/caduceus.opt 
CADUCEUSLIB=../../lib/why
EXECCADUCEUS=CADUCEUSLIB=$(CADUCEUSLIB) $(CADUCEUS)

test:
	-gcc -ansi -pedantic -Wall -c test.c
	$(EXECCADUCEUS) -v -type-only test.c

gcc:
	gcc -Wall test.c && ./a.out

test.i: test.c
	gcc -E $^ > $@
