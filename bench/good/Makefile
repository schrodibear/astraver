
all:
	for f in *.mlw; do make `basename $$f .mlw`_valid.vo; done

bench:
	cd ..; ./bench ../bin/why.opt

tc:
	cd ..; ./bench "../bin/why.opt -tc"

WHY=../../bin/why.opt

GWHY=../../bin/gwhy.opt

%_why.v %_valid.v: %.mlw $(WHY)
	$(WHY) -V -d --coq-v8 --valid --coq-tactic intuition $<

%_why.vo: %_why.v
	coqc -I ../../lib/coq $<

%_valid.vo: %_valid.v %_why.vo
	coqc -I ../../lib/coq $<


interval_arith_full_why.v: interval_arith_full.why $(WHY)
	$(WHY) -V --coq-v8 --coq-tactic intros -split-user-conj ../../lib/why/floats_full.why $<

interval_arith_full.gui: interval_arith_full.why $(GWHY)
	WHYLIB=../../lib $(GWHY) -split-user-conj -V ../../lib/why/floats_full.why $<

floats1_why.v: floats1.why $(WHY)
	$(WHY) -V --coq-v8 --coq-tactic intuition ../../lib/why/floats_full.why $<

floats1.gui: floats1.why $(GWHY)
	WHYLIB=../../lib $(GWHY) -split-user-conj -V ../../lib/why/floats_full.why $<

