
all:
	../../bin/why.opt -d -V all.ml

bench:
	cd ..; ./bench ../bin/why.opt

tc:
	cd ..; ./bench "../bin/why.opt -tc"

WHY=../../bin/why.opt

%_why.v: %.ml $(WHY)
	$(WHY) -V $<

%.vo: %.v
	coqc -I ../../lib/coq $<
