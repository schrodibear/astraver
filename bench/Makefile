
all:
	./bench "../bin/why.opt --valid"

tc:
	./bench "../bin/why.opt -tc"

ml:
	../bin/why.opt --ocaml test.mlw

c:
	../bin/why.opt -d -V --coq-tactic Magic ctest.c
	coqc -R ../lib/coq Coq.why ctest_why.v
	#coqide ctest_why.v

pvs:
	../bin/why.opt --pvs -d -V test.mlw
	pvs -batch -v 3 -l batch.el

c-pvs:
	../bin/why.opt --pvs -d -V ctest.c
	pvs -batch -v 3 -l batch.el

harvey:
	../bin/why.opt --harvey -d -V test.mlw

hol:
	../bin/why.opt --hol-light -d -V test.mlw

test:
	../bin/why.opt -d -V --valid --coq-tactic Magic test.mlw
	coqc -R ../lib/coq Coq.why test_why.v
	coqc -R ../lib/coq Coq.why test_valid.v
