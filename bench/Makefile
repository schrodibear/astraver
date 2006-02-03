
WHY=WHYLIB=../lib/why ../bin/why.opt
BWHY=WHYLIB=../lib/why ../bin/why.byte

all:
	./bench "../bin/why.opt --coq-v8 --valid"

tc:
	./bench "../bin/why.opt -tc"

ml:
	../bin/why.opt --ocaml test.mlw > test.ml
	ocamlc -c -i test.ml

.PHONY: c

c:
	gcc -c ctest.c
	../bin/caduceus.opt -parse-only ctest.c
# 	../bin/why.opt --coq-v8 -d -V --valid --coq-tactic magic ctest.c
# 	coqc -R ../lib/coq Coq.why ctest_why.v
# 	coqc -R ../lib/coq Coq.why ctest_valid.v
# 	#coqide ctest_why.v
# 	../bin/why.opt --ocaml ctest.c > ctest.ml
# 	ocamlc -c -i ctest.ml

pvs:
	../bin/why.opt --pvs -d -V test.mlw
	pvs -batch -v 3 -l batch.el

isabelle:
	../bin/why.opt --isabelle -d -V test.mlw

c-pvs:
	../bin/why.opt --pvs -d -V ctest.c
	pvs -batch -v 3 -l batch.el

harvey:
	../bin/why.opt --harvey -d -V test.mlw
	../bin/dp.opt test_why.rv

simplify:
	../bin/why.opt --simplify -d -V test.mlw
	../bin/dp.opt test_why.sx

cvcl:
	../bin/why.opt --cvcl -d -V test.mlw
	../bin/dp.opt test_why.cvc

mizar:
	../bin/why.opt --mizar -d -V test.mlw
	mzf test_why.miz

hol:
	../bin/why.opt --hol-light -d -V test.mlw

test:
#	$(WHY) --coq-v8 -d -V --coq-tactic magic test.mlw
	$(WHY) --coq-v8 -d -V --valid --coq-tactic magic test.mlw
	coqc -I ../lib/coq test_why.v || coqide -I ../lib/coq test_why.v
	coqc -I ../lib/coq test_valid.v

partial:
	$(WHY) --coq-v8 -d -V --partial --valid --coq-tactic magic test.mlw
	coqc -I ../lib/coq test_why.v || coqide -I ../lib/coq test_why.v
	coqc -I ../lib/coq test_valid.v

total:
	$(WHY) --coq-v8 -d -V --total --valid --coq-tactic magic test.mlw
	coqc -I ../lib/coq test_why.v || coqide -I ../lib/coq test_why.v
	coqc -I ../lib/coq test_valid.v

byte:
	$(BWHY) --coq-v8 -d -V --valid --coq-tactic magic test.mlw
	-coqc -I ../lib/coq test_why.v || coqide -I ../lib/coq test_why.v
	-coqc -I ../lib/coq test_valid.v

stat:
	../bin/gwhy.opt -d test.mlw
