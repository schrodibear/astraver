
CADUCEUS=../../../bin/caduceus.opt

%.why %_valid.v: %.c $(CADUCEUS)
	$(CADUCEUS) $<

WHY=../../../bin/why.opt

%_why.v %_valid.v: %.why $(WHY)
	$(WHY) --valid -V --coq-v8 $<

%_valid.vo: %_why.vo

%.vo: %.v
	coqc -R ../../lib/coq Coq.why $<

