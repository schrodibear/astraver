
all:
	../../bin/why.opt -d -V --coq-v8 --valid all.mlw
	coqc -R ../../lib/coq Coq.why all_why.v

bench:
	cd ..; ./bench ../bin/why.opt

tc:
	cd ..; ./bench "../bin/why.opt -tc"

WHY=../../bin/why.opt

%_why.v %_valid.v: %.mlw $(WHY)
	$(WHY) --valid -V --coq-v8 $<

%.vo: %.v
	coqc -R ../../lib/coq Coq.why $<
