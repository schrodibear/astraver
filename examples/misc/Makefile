
all: swap_why.vo

%_why.v: %.ml
	time ../../bin/why.opt -V $<

%.vo: %.v
	time coqc $<
