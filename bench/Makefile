
WHY=WHYLIB=../lib ../bin/why.opt
BWHY=WHYLIB=../lib ../bin/why.byte
GWHY=WHYLIB=../lib ../bin/gwhy.opt

all:
	./bench "../bin/why.opt --coq-v8 --valid"

tc:
	./bench "../bin/why.opt -tc"

ml:
	../bin/why.opt --ocaml test.mlw > test.ml
	ocamlc -c -i test.ml

.PHONY: c ml

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
	rm -f *.baf
	../bin/why-dp.opt test_why.rv

simplify:
	../bin/why.opt --simplify -d -V test.mlw
	Simplify test_why.sx

yices:
	../bin/why.opt --smtlib --encoding sstrat test.mlw
	../bin/why-dp.opt test_why.smt

ergo:
	../bin/why.opt --why test.mlw
	alt-ergo test_why.why

rv-sat:
	../bin/why.opt --smtlib -d --encoding mono -V test.mlw
	../bin/why-dp.opt test_why.smt
cvcl:
	../bin/why.opt --cvcl -d -V test.mlw
	../bin/why-dp.opt test_why.cvc

cvc3:
	../bin/why.opt --cvcl -d -V test.mlw
	../bin/why-dp.opt test_why.cvc

mizar:
	../bin/why.opt --mizar -d -V test.mlw
	mzf test_why.miz

hol:
	../bin/why.opt --hol-light -d -V test.mlw

gappa:
	../bin/why.opt --gappa -d -V test.mlw
	gappa < test_why_po_1.gappa

test:
#	$(WHY) --coq-v8 -d -V --coq-tactic magic test.mlw
	$(WHY) --coq-v8 -d -V --valid --coq-tactic admit test.mlw
	coqc -I ../lib/coq test_why.v || coqide -I ../lib/coq test_why.v
	coqc -I ../lib/coq test_valid.v

fwp: fastwp.simplify

fastwp.simplify:
	$(BWHY) --why -d -V --fast-wp --all-vc test.mlw
	$(BWHY) --no-prelude -tc test_why.why
	$(BWHY) --simplify --fast-wp --all-vc test.mlw
	../bin/why-dp.opt -no-timings test_why.sx

fastwp.ergo:
	$(BWHY) --why -d --fast-wp test.mlw
	$(BWHY) -no-prelude -tc test_why.why
	$(BWHY) --alt-ergo --fast-wp --all-vc test.mlw
	../bin/why-dp.opt -no-timings test_why.why

FASTWPBENCH=po oldify opaque inductive \
	wpcalls exns loops poly see all set return \
        complex_arg_1 complex_arg_2 recfun
fastwp.bench.simplify:
	rm -f good/*_why.sx
	for f in $(FASTWPBENCH) ; do \
	  $(BWHY) --simplify --fast-wp good/$$f.mlw; \
	done
	why-dp -no-timings good/*_why.sx

fastwp.bench.ergo:
	rm -f good/*_why.why
	for f in $(FASTWPBENCH) ; do \
	  $(WHY) --alt-ergo --fast-wp good/$$f.mlw; \
	done
	../bin/why-dp.opt -no-timings good/*_why.why

partial:
	$(WHY) --coq-v8 -d -V --partial --valid --coq-tactic admit test.mlw
	coqc -I ../lib/coq test_why.v || coqide -I ../lib/coq test_why.v
	coqc -I ../lib/coq test_valid.v

total:
	$(WHY) --coq-v8 -d -V --total --valid --coq-tactic admit test.mlw
	coqc -I ../lib/coq test_why.v || coqide -I ../lib/coq test_why.v
	coqc -I ../lib/coq test_valid.v

byte:
	$(BWHY) --coq-v8 -d -V --valid --coq-tactic admit test.mlw
	-coqc -I ../lib/coq test_why.v || coqide -I ../lib/coq test_why.v
	-coqc -I ../lib/coq test_valid.v

gwhy:
	../bin/gwhy.opt -d -all-vc test.mlw

zenon:
	../bin/why.opt -d -V --zenon test.mlw
	timeout 10 zenon test_why.znn

#rv-sat:
#	../bin/why.opt -d -V --encoding mono --smtlib test.mlw
#	rv-sat test_why.smt
