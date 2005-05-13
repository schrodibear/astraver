# this makefile was automatically generated; do not edit 

WHY=why 

CADULIB=/users/demons/filliatr/local/soft/why/lib

COQTACTIC=intuition

.PHONY: all coq pvs simplify cvcl harvey smtlib

all: simplify/g4_why.sx

coq: coq/g4_why.vo

coq/%_why.v: why/%_spec.why why/%.why
	@echo 'why -coq-v8 [...] why/$*.why' &&$(WHY) -coq-v8 -dir coq -coq-preamble "Require Export $*_spec_why." -coq-tactic "$(COQTACTIC)" $(CADULIB)/why/caduceus.why why/$*_spec.why why/$*.why

coq/%_spec_why.v: why/%_spec.why
	@echo 'why -coq-v8 [...] why/$*_spec.why' && $(WHY) -coq-v8 -dir coq -coq-preamble "Require Export Caduceus." $(CADULIB)/why/caduceus.why why/$*_spec.why

coq/%.vo: coq/%.v
	coqc -I coq $<

pvs: pvs/g4_why.pvs

pvs/%_why.pvs: pvs/%_spec_why.pvs why/%.why
	$(WHY) -pvs -dir pvs -pvs-preamble "importing $*_spec_why" $(CADULIB)/why/caduceus.why why/$*_spec.why why/$*.why

pvs/%_spec_why.pvs: pvs/caduceus_why.pvs why/%_spec.why
	$(WHY) -pvs -dir pvs -pvs-preamble "importing caduceus_why" $(CADULIB)/why/caduceus.why why/$*_spec.why

pvs/caduceus_why.pvs:
	$(WHY) -pvs -dir pvs $(CADULIB)/why/caduceus.why

simplify: simplify/g4_why.sx.all
	@echo 'Running Simplify on proof obligations' && (dp -timeout 10 $^)

simplify/%_why.sx.all: simplify/%_why.sx
	@cat simplify/caduceus_why.sx simplify/$*_spec_why.sx $< > $@

simplify/%_why.sx: why/%_spec.why why/%.why
	@echo 'why -simplify [...] why/$*.why' && $(WHY) -simplify -no-simplify-prelude -dir simplify $(CADULIB)/why/caduceus.why why/$*_spec.why why/$*.why

cvcl: cvcl/g4_why.cvc.all

	@echo 'Running CVC Lite on proof obligations' && (dp -timeout 10 $^)

cvcl/%_why.cvc.all: cvcl/%_why.cvc
	@cat cvcl/caduceus_why.cvc cvcl/$*_spec_why.cvc $< > $@

cvcl/%_why.cvc: why/%_spec.why why/%.why
	@echo 'why -cvcl [...] why/$*.why' && $(WHY) -cvcl -no-cvcl-prelude -dir cvcl $(CADULIB)/why/caduceus.why why/$*_spec.why why/$*.why

harvey: harvey/g4_why.all.rv
	@echo 'Running haRVey on proof obligations' && (dp -timeout 10 $^)

harvey/%_why.all.rv: harvey/%_why.rv
	@rv_merge harvey/caduceus_why.rv harvey/$*_spec_why.rv $< > $@

harvey/%_why.rv: why/%_spec.why why/%.why
	@echo 'why -harvey [...] why/$*.why' && $(WHY) -harvey -dir harvey $(CADULIB)/why/caduceus.why why/$*_spec.why why/$*.why

smtlib: smtlib/g4_why.smt

smtlib/%_why.smt: why/%_spec.why why/%.why
	@echo 'why -smtlib [...] why/$*.why' && $(WHY) -smtlib -dir smtlib $(CADULIB)/why/caduceus.why why/$*_spec.why why/$*.why

include g4.depend

depend g4.depend: coq/g4_spec_why.v coq/g4_why.v
	-coqdep -I coq coq/*.v > g4.depend

clean:
	rm -f coq/*.vo

