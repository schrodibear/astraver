
all:
	for f in *.mlw; do make `basename $$f .mlw`_valid.vo; done

bench:
	cd ..; ./bench ../bin/why.opt

tc:
	cd ..; ./bench "../bin/why.opt -tc"

WHY=../../bin/why.opt

%_why.v %_valid.v: %.mlw $(WHY)
	$(WHY) -V -d --coq-v8 --valid --coq-tactic intuition $<

%_why.vo: %_why.v
	coqc -I ../../lib/coq $<

%_valid.vo: %_valid.v %_why.vo
	coqc -I ../../lib/coq $<

