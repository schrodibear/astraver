
all:
	./bench "../bin/why.opt --valid"

tc:
	./bench "../bin/why.opt -tc"

ml:
	../bin/why.opt --ocaml test.mlw

test:
	../bin/why.opt -d -V --valid --coq-tactic Magic test.mlw
	coqc -I ../lib/coq test_why.v
