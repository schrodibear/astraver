
all:
	./bench "../bin/why.opt --valid"

tc:
	./bench "../bin/why.opt -tc"

ml:
	../bin/why.opt --ocaml test.mlw

c:
	../bin/why.opt ctest.c

test:
	../bin/why.opt -d -V --valid --coq-tactic Magic test.mlw
	coqc -R ../lib/coq Coq.why test_why.v
