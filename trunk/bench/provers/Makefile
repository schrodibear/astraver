
PROVERS=coq simplify zenon harvey cvcl isabelle hol-light mizar

all:
	for p in $(PROVERS); do \
	  ../../bin/why.opt --$$p everything.mlw; \
	done

gui:
	make -C ../.. gwhy
	../../bin/gwhy.opt everything.mlw

simplify:
	../../bin/why.opt --simplify everything.mlw
	dp everything_why.sx

zenon:
	../../bin/why.opt --zenon everything.mlw
	dp everything_why.znn

cvcl:
	../../bin/why.opt --cvcl everything.mlw
	dp everything_why.cvc

harvey:
	../../bin/why.opt --harvey everything.mlw
	dp everything_why.rv
	rm -f *.baf
