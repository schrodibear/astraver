
all:
	./bench "../bin/why.opt --valid"

tc:
	./bench "../bin/why.opt -tc"

test:
	../bin/why.opt -d -V --valid test.ml
	coqc -I ../lib/coq test_why.v
