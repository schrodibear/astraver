
test:
	-gcc -c test.c
	../../bin/caduceus.opt test.c

gcc:
	gcc test.c && ./a.out

test.i: test.c
	gcc -E $^ > $@
