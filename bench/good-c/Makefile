
WHY=../../bin/why.opt

%_why.v: %.c $(WHY)
	$(WHY) --coq-tactic Intuition --valid -V $<

%.vo: %.v
	coqc -R ../../lib/coq Coq.why $<
