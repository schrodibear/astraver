
WHY=../../bin/why.opt

%_why.v: %.ml $(WHY)
	time $(WHY) -V $<

%.vo: %.v
	time coqc $<
