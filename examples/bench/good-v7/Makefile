
all:
	../../bin/why.opt -d -V --valid all.mlw
	coqc -v7 -R ../../lib/coq Coq.why all_why.v

bench:
	cd ..; ./bench ../bin/why.opt

tc:
	cd ..; ./bench "../bin/why.opt -tc"

WHY=../../bin/why.opt

%_why.v %_valid.v: %.mlw $(WHY)
	$(WHY) --valid -V $<

%.vo: %.v
	coqc -v7 -R ../../lib/coq Coq.why $<
