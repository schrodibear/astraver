
all:
	./bench "../bin/why.opt --valid"

tc:
	./bench "../bin/why.opt -tc"

ml:
	../bin/why.opt --ocaml test.mlw

c:
	../bin/why.opt -d -V --coq-tactic Intuition ctest.c
	coqc -R ../lib/coq Coq.why ctest_why.v

pvs:
	../bin/why.opt --pvs -d -V test.mlw
	pvs -batch -v 3 -l batch.el

test:
	../bin/why.opt -d -V --valid --coq-tactic Magic test.mlw
	coqc -R ../lib/coq Coq.why test_why.v
