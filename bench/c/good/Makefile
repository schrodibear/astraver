
WHY=../../bin/why.opt

%_why.v %_valid.v: %.c $(WHY)
	$(WHY) --coq-v8 --coq-tactic intuition --valid -V $<

%_valid.vo: %_why.vo

%.vo: %.v
	coqc -R ../../lib/coq Coq.why $<

