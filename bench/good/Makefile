
all:
	../../bin/why.opt -d -V --valid all.mlw
	coqc -I ../../lib/coq all_why.v

bench:
	cd ..; ./bench ../bin/why.opt

tc:
	cd ..; ./bench "../bin/why.opt -tc"

WHY=../../bin/why.opt

%_why.v: %.mlw $(WHY)
	$(WHY) --valid -V $<

%.vo: %.v
	coqc -I ../../lib/coq $<
