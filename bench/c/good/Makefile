
CADUCEUS=../../../bin/caduceus.opt 
CADUCEUSLIB=../../../lib/

all: coq/struct_why.vo coq/pointer_why.vo

purse: why/purse.why coq/caduceus_spec_why.v coq/purse_why.vo


EXECCADUCEUS=CADUCEUSLIB=$(CADUCEUSLIB) $(CADUCEUS)

why/%.why: %.c $(CADUCEUS) $(CADUCEUSLIB)/why/caduceus.why
	$(EXECCADUCEUS) $<

WHY=../../../bin/why.opt

coq/caduceus_spec_why.v: why/caduceus_spec.why $(WHY)
	$(WHY) -dir coq --valid -V --coq-v8 --coq-preamble "Require Export caduceus_why." why/caduceus.why $<

coq/%_why.v coq/%_valid.v: why/%.why $(WHY)
	$(WHY) -dir coq --valid -V --coq-v8 --coq-preamble "Require Export caduceus_spec_why." why/caduceus.why why/caduceus_spec.why $<

simplify/%_why.sx: why/%.why $(WHY)
	$(WHY) -dir simplify -V --simplify --no-simplify-prelude why/caduceus.why why/caduceus_spec.why $<

coq/caduceus_why.v: why/caduceus.why $(WHY)
	$(WHY) -dir coq --coq-v8 why/caduceus.why

coq/%_valid.vo: coq/%_why.vo

coq/%.vo: coq/%.v
	coqc -R ../../../lib/coq Coq.why -I coq $<

simplify:
	time make do_simplify > simplify.log
	@echo -n "valid obligations: " 
	@egrep '[0-9]+: Valid.$$' simplify.log | wc -l
	@echo -n "invalid obligations: " 
	@egrep '[0-9]+: Invalid.$$' simplify.log | wc -l

do_simplify: simplify/all_why.sxcheck    \
	     simplify/continue_why.sxcheck  \
	     simplify/passing_why.sxcheck  \
	     simplify/rec_why.sxcheck \
	     simplify/see_why.sxcheck \
	     simplify/sum1_why.sxcheck \
	     simplify/arith_why.sxcheck \
	     simplify/pointer_why.sxcheck \
	     simplify/struct_why.sxcheck \
	     simplify/break_why.sxcheck \
	     simplify/dowhile_why.sxcheck \
	     simplify/purse_why.sxcheck \
	     simplify/schorr_waite_why.sxcheck \
	     simplify/call_why.sxcheck \
             simplify/rec2_why.sxcheck \
	     simplify/search_why.sxcheck \
	     simplify/flag_why.sxcheck \
	     simplify/sum2_why.sxcheck \
	     simplify/skip_lists_why.sxcheck \
	     simplify/cyclic_why.sxcheck \
	     simplify/sort_why.sxcheck \
	     simplify/rev_why.sxcheck

simplify/%.sxcheck: simplify/%.sx
	cat simplify/caduceus_why.sx simplify/caduceus_spec_why.sx $< > $<.all
	Simplify $<.all

type-all:
	export CADUCEUSLIB=../../../lib/why; \
	for f in *.c; do \
	  $(CADUCEUS) -type-only $$f; \
	done

include .depend

depend .depend:
	coqdep -R ../../../lib/coq Coq.why -I coq coq/*.v > .depend

clean:
	rm -f why/*.why coq/*.vo coq/caduceus_why.v coq/caduceus_spec_why.v
