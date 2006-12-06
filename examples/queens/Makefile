
WHY=../../bin/why.opt
GWHY=../../bin/gwhy.opt
OPT=--no-arrays

gwhy:
	$(GWHY) $(OPT) queens.why

gwhy.split:
	$(GWHY) $(OPT) -split-user-conj queens.why

coq:
	$(WHY) $(OPT) --coq --coq-tactic "admit" queens.why
	coqide queens_why.v

coq.split:
	$(WHY) $(OPT) -split-user-conj --coq --coq-tactic "admit" queens.why
	coqide queens_why.v
