
CADUCEUS=../../../bin/caduceus.opt

%_why.v %_valid.v: %.c $(WHY)
	$(CADUCEUS) $<

%_valid.vo: %_why.vo

%.vo: %.v
	coqc -R ../../lib/coq Coq.why $<

