
CADUCEUS=../../../bin/caduceus.opt

%.why %_valid.v: %.c $(CADUCEUS)
	$(CADUCEUS) $<

WHY=../../../bin/why.opt

%_why.v %_valid.v: %.why $(WHY)
	$(WHY) --valid -V --coq-v8 theory.why $<

theory_why.v: theory.why $(WHY)
	$(WHY) --coq-v8 theory.why

%_valid.vo: %_why.vo

%.vo: %.v
	coqc -R ../../../lib/coq Coq.why $<

sum2.why: theory.why

include .depend

depend .depend:
	coqdep *.v > .depend
