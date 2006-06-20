# this makefile was automatically generated; do not edit 

WHY=why --fp 

GWHY=gwhy --fp 

CADULIB=/users/homepc9-152/jcf/soft/why-flottants/examples-c/g4/../../lib

COQTACTIC=intuition

COQDEP=coqdep -I `coqc -where`/user-contrib

.PHONY: all coq pvs simplify cvcl harvey smtlib zenon

all: simplify/g4_why.sx

coq: coq/g4_why.vo

coq/%_spec_why.v: why/%_spec.why
	@echo 'why -coq-v8 [...] why/$*_spec.why' && $(WHY) -coq-v8 -dir coq -coq-preamble "Require Export Caduceus." $(CADULIB)/why/caduceus.why why/$*_spec.why

coq/%_why.v: why/g4_spec.why why/%.why
	@echo 'why -coq-v8 [...] why/$*.why' &&$(WHY) -coq-v8 -dir coq -coq-preamble "Require Export g4_spec_why." -coq-tactic "$(COQTACTIC)" $(CADULIB)/why/caduceus.why why/g4_spec.why why/$*.why

coq/%.vo: coq/%.v
	coqc -I coq $<

pvs: pvs/g4_why.pvs

pvs/%_spec_why.pvs: why/%_spec.why
	$(WHY) -pvs -dir pvs -pvs-preamble "importing caduceus_why" $(CADULIB)/why/caduceus.why why/$*_spec.why

pvs/%_why.pvs: pvs/g4_spec_why.pvs why/%.why
	$(WHY) -pvs -dir pvs -pvs-preamble "importing g4_spec_why" $(CADULIB)/why/caduceus.why why/g4_spec.why why/$*.why

pvs/caduceus_why.pvs:
	$(WHY) -pvs -dir pvs $(CADULIB)/why/caduceus.why

isabelle: isabelle/g4_why.thy isabelle/g4_spec_why.thy

isabelle/%_spec_why.thy: why/%_spec.why
	$(WHY) -isabelle -dir isabelle -isabelle-base-theory caduceus_why $(CADULIB)/why/caduceus.why why/$*_spec.why

isabelle/%_why.thy: isabelle/g4_spec_why.thy why/%.why
	$(WHY) -isabelle -dir isabelle -isabelle-base-theory g4_spec_why $(CADULIB)/why/caduceus.why why/g4_spec.why why/$*.why
	cp -f /users/homepc9-152/jcf/soft/why-flottants/examples-c/g4/../../lib/isabelle/caduceus_why.thy isabelle/

simplify: simplify/g4_why.sx
	@echo 'Running Simplify on proof obligations' && (dp -timeout 10 $^)

simplify/%_why.sx: why/g4_spec.why why/%.why
	@echo 'why -simplify [...] why/$*.why' && $(WHY) -simplify -no-simplify-prelude -dir simplify $(CADULIB)/why/caduceus.why why/g4_spec.why why/$*.why

goals: why/g4_why.why

why/%_why.why: why/g4_spec.why why/%.why
	@echo 'why --why [...] why/$*.why' && $(WHY) --why -dir why $(CADULIB)/why/caduceus.why why/g4_spec.why why/$*.why

cvcl: cvcl/g4_why.cvc

	@echo 'Running CVC Lite on proof obligations' && (dp -timeout 10 $^)

cvcl/%_why.cvc: why/g4_spec.why why/%.why
	@echo 'why -cvcl [...] why/$*.why' && $(WHY) -cvcl -dir cvcl $(CADULIB)/why/caduceus.why why/g4_spec.why why/$*.why

harvey: harvey/g4_why.rv
	@echo 'Running haRVey on proof obligations' && (dp -timeout 10 $^)

harvey/%_why.rv: why/g4_spec.why why/%.why
	@echo 'why -harvey [...] why/$*.why' && $(WHY) -harvey -dir harvey $(CADULIB)/why/caduceus.why why/g4_spec.why why/$*.why

zenon: zenon/g4_why.znn
	@echo 'Running Zenon on proof obligations' && (dp -timeout 10 $^)

zenon/%_why.znn: why/g4_spec.why why/%.why
	@echo 'why -zenon [...] why/$*.why' && $(WHY) -zenon -dir zenon $(CADULIB)/why/caduceus.why why/g4_spec.why why/$*.why

smtlib: smtlib/g4_why.smt

smtlib/%_why.smt: why/g4_spec.why why/%.why
	@echo 'why -smtlib [...] why/$*.why' && $(WHY) -smtlib -dir smtlib $(CADULIB)/why/caduceus.why why/g4_spec.why why/$*.why

gui stat: g4.stat

%.stat: why/g4_spec.why why/%.why
	@echo 'gwhy [...] why/$*.why' && $(GWHY) $(CADULIB)/why/caduceus.why why/g4_spec.why why/$*.why

include g4.depend

depend g4.depend: coq/g4_spec_why.v coq/g4_why.v
	-$(COQDEP) -I coq coq/g4*_why.v > g4.depend

clean:
	rm -f coq/*.vo

