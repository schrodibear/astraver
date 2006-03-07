
PROVERS=coq simplify zenon harvey cvcl isabelle hol4 hol-light mizar smtlib

all:
	for p in $(PROVERS); do \
	  ../../bin/why.opt --$$p everything.mlw; \
	done
