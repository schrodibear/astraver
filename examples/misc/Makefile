
WHY=../../bin/why.opt

all: swap_why.vo loop0_why.vo

%_why.v: %.ml $(WHY)
	time $(WHY) -V $<

%.vo: %.v
	time coqc $<
