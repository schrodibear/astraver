
all:
	./bench "../bin/why.opt --valid"

tc:
	./bench "../bin/why.opt -tc"

ml:
	../bin/why.opt --ocaml test.mlw > test.ml
	ocamlc -c -i test.ml

c:
	../bin/why.opt -d -V --valid --coq-tactic Magic ctest.c
	coqc -R ../lib/coq Coq.why ctest_why.v
	coqc -R ../lib/coq Coq.why ctest_valid.v
	#coqide ctest_why.v
	../bin/why.opt --ocaml ctest.c > ctest.ml
	ocamlc -c -i ctest.ml

pvs:
	../bin/why.opt --pvs -d -V test.mlw
	pvs -batch -v 3 -l batch.el

c-pvs:
	../bin/why.opt --pvs -d -V ctest.c
	pvs -batch -v 3 -l batch.el

harvey:
	../bin/why.opt --harvey -d -V test.mlw
	for f in test*.rv; do rvc $$f; done

simplify:
	../bin/why.opt --simplify -d -V test.mlw
	Simplify test_why.sx

mizar:
	../bin/why.opt --mizar -d -V test.mlw
	mzf test_why.miz

hol:
	../bin/why.opt --hol-light -d -V test.mlw

test:
	../bin/why.opt -d -V --valid --coq-tactic Magic test.mlw
	coqc -R ../lib/coq Coq.why test_why.v
	coqc -R ../lib/coq Coq.why test_valid.v
