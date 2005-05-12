# this makefile was automatically generated; do not edit 

WHY=why 

CADULIB=/home/jc/soft/why/lib

COQTACTIC=intuition

.PHONY: all coq pvs simplify cvcl harvey

all: coq/caduceus_spec_why.v simplify/g4_why.sx

coq: coq/g4_why.vo

coq/%_why.v: coq/caduceus_spec_why.v why/caduceus_spec.why why/%.why
	@echo 'why -coq-v8 [...] why/$*.why' &&$(WHY) -coq-v8 -dir coq -coq-preamble "Require Export caduceus_spec_why." -coq-tactic "$(COQTACTIC)" $(CADULIB)/why/caduceus.why why/caduceus_spec.why why/$*.why

coq/caduceus_spec_why.v: why/caduceus_spec.why
	@echo 'why -coq-v8 [...] why/caduceus_spec.why' && $(WHY) -coq-v8 -dir coq -coq-preamble "Require Export caduceus_why. Require Export caduceus_tactics." $(CADULIB)/why/caduceus.why why/caduceus_spec.why

coq/%.vo: coq/%.v
	coqc -I coq $<

pvs: pvs/g4_why.pvs

pvs/%_why.pvs: pvs/caduceus_spec_why.pvs why/%.why
	$(WHY) -pvs -dir pvs -pvs-preamble "importing caduceus_spec_why" $(CADULIB)/why/caduceus.why why/caduceus_spec.why why/$*.why

pvs/caduceus_spec_why.pvs: pvs/caduceus_why.pvs why/caduceus_spec.why
	$(WHY) -pvs -dir pvs -pvs-preamble "importing caduceus_why" $(CADULIB)/why/caduceus.why why/caduceus_spec.why

pvs/caduceus_why.pvs:
	$(WHY) -pvs -dir pvs $(CADULIB)/why/caduceus.why

simplify: simplify/g4_why.sx.all
	@echo 'Running Simplify on proof obligations' && (dp -timeout 10 $^)

simplify/%_why.sx.all: simplify/%_why.sx
	@cat simplify/caduceus_why.sx simplify/caduceus_spec_why.sx $< > $@

simplify/%_why.sx: why/caduceus_spec.why why/%.why
	@echo 'why -simplify [...] why/$*.why' && $(WHY) -simplify -no-simplify-prelude -dir simplify $(CADULIB)/why/caduceus.why why/caduceus_spec.why why/$*.why

cvcl: cvcl/g4_why.cvc.all

	@echo 'Running CVC Lite on proof obligations' && (dp -timeout 10 $^)

cvcl/%_why.cvc.all: cvcl/%_why.cvc
	@cat cvcl/caduceus_why.cvc cvcl/caduceus_spec_why.cvc $< > $@

cvcl/%_why.cvc: why/caduceus_spec.why why/%.why
	@echo 'why -cvcl [...] why/$*.why' && $(WHY) -cvcl -no-cvcl-prelude -dir cvcl $(CADULIB)/why/caduceus.why why/caduceus_spec.why why/$*.why

harvey: harvey/g4_why.all.rv
	@echo 'Running Simplify on proof obligations' && (dp -timeout 10 $^)

harvey/%_why.all.rv: harvey/%_why.rv
	@rv_merge harvey/caduceus_why.rv harvey/caduceus_spec_why.rv $< > $@

harvey/%_why.rv: why/caduceus_spec.why why/%.why
	@echo 'why -harvey [...] why/$*.why' && $(WHY) -harvey -dir harvey $(CADULIB)/why/caduceus.why why/caduceus_spec.why why/$*.why

include g4.depend

depend g4.depend: coq/caduceus_spec_why.v coq/caduceus_tactics.v coq/g4_why.v
	-coqdep -I coq coq/*.v > g4.depend

clean:
	rm -f coq/*.vo

