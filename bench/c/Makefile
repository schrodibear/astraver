
test:
	-gcc -Wall -c test.c
	../../bin/caduceus.opt -v -type-only test.c

gcc:
	gcc -Wall test.c && ./a.out

test.i: test.c
	gcc -E $^ > $@
