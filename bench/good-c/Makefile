
WHY=../../bin/why.opt

%_why.v: %.c $(WHY)
	$(WHY) -V $<

%.vo: %.v
	coqc -R ../../lib/coq Coq.why $<
