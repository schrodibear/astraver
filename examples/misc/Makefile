
all: swap_why.vo

%_why.v: %.ml
	../../bin/why.opt -d -V $<

%.vo: %.v
	coqc $<
