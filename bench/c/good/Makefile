
CADUCEUS=../../../bin/caduceus.opt 
CADUCEUSLIB=../../../lib/why

all: pointer_why.vo

EXECCADUCEUS=CADUCEUSLIB=$(CADUCEUSLIB) $(CADUCEUS)

%.why %_valid.v: %.c $(CADUCEUS) $(CADUCEUSLIB)/caduceus.why
	$(EXECCADUCEUS) $<

WHY=../../../bin/why.opt

%_why.v %_valid.v: %.why $(WHY)
	$(WHY) --valid -V --coq-v8 --coq-preamble "Require Export Why" caduceus.why $<

%_why.sx: %.why $(WHY)
	$(WHY) -V --simplify --no-simplify-prelude caduceus.why $<

caduceus_why.v: caduceus.why $(WHY)
	$(WHY) --coq-v8 caduceus.why

%_valid.vo: %_why.vo

%.vo: %.v
	coqc -R ../../../lib/coq Coq.why $<

simplify:
	time make do_simplify > simplify.log
	@echo -n "valid obligations: " 
	@egrep '[0-9]+: Valid.$$' simplify.log | wc -l
	@echo -n "invalid obligations: " 
	@egrep '[0-9]+: Invalid.$$' simplify.log | wc -l

do_simplify: arith_why.sxcheck sum2_why.sxcheck pointer_why.sxcheck

%.sxcheck: %.sx
	cat caduceus_why.sx $< > $<.all
	Simplify $<.all

type-all:
	export CADUCEUSLIB=../../../lib/why; \
	for f in *.c; do \
	  $(CADUCEUS) -type-only $$f; \
	done

include .depend

depend .depend:
	coqdep *.v > .depend
