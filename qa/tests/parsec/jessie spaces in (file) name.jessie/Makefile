# this makefile was automatically generated; do not edit 

TIMEOUT ?= 10

DP ?= why-dp -timeout $(TIMEOUT)
WHYEXEC ?= why
GWHYEXEC ?= gwhy-bin
WHYLIB ?= /home/mikhail/.opam/4.02.1/lib/why

USERWHYTWOOPT=
USERWHYTHREEOPT=
WHY=WHYLIB=$(WHYLIB) $(WHYEXEC) $(WHYOPT) $(USERWHYTWOOPT) -explain -locs jessie-spaces-in--file--name.loc

GWHY=WHYLIB=$(WHYLIB) $(GWHYEXEC) $(WHYOPT) $(USERWHYTWOOPT) -explain -locs jessie-spaces-in--file--name.loc

JESSIELIBFILES ?= $(WHYLIB)/why/jessie.why
JESSIE3CONF ?= $(WHYLIB)/why3/why3.conf

COQDEP = coqdep

.PHONY: all coq pvs simplify vampire cvcl harvey smtlib zenon

all: simplify/jessie-spaces-in--file--name_why.sx

project: why/jessie-spaces-in--file--name.wpr

why/%.wpr:  WHYOPT=--project -dir why
why/%.wpr: why/%.why
	@echo 'why --project [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why

goals: why/jessie-spaces-in--file--name_ctx.why

why/%_ctx.why: WHYOPT=--multi-why -dir why
why/%_ctx.why: why/%.why
	@echo 'why --multi-why [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why

coq: coq/jessie-spaces-in--file--name_why.vo

coq/jessie-spaces-in--file--name_why.v: WHYOPT=-coq -dir coq -coq-preamble "Require Export jessie_why." -coq-tactic "intuition"
coq/jessie-spaces-in--file--name_why.v: why/jessie-spaces-in--file--name.why
	@echo 'why -coq [...] why/jessie-spaces-in--file--name.why' && $(WHY) $(JESSIELIBFILES) why/jessie-spaces-in--file--name.why && rm -f coq/jessie_why.v

coq-goals: goals coq/jessie-spaces-in--file--name_ctx_why.vo
	for f in why/*_po*.why; do make -f jessie-spaces-in--file--name.makefile coq/`basename $$f .why`_why.v ; done

coq/jessie-spaces-in--file--name_ctx_why.v: WHYOPT=-no-pervasives -coq -dir coq -coq-preamble "Require Export jessie_why." -coq-tactic "intuition"
coq/jessie-spaces-in--file--name_ctx_why.v: why/jessie-spaces-in--file--name_ctx.why
	@echo 'why -coq [...] why/jessie-spaces-in--file--name_ctx.why' && $(WHY) why/jessie-spaces-in--file--name_ctx.why

coq/%_why.v: WHYOPT=-no-pervasives -coq -dir coq -coq-preamble "Require Export jessie-spaces-in--file--name_ctx_why." -coq-tactic "intuition"
coq/%_why.v: why/%.why
	@echo 'why -coq [...] why/$*.why' && $(WHY) why/jessie-spaces-in--file--name_ctx.why why/$*.why

coq/%.vo: coq/%.v
	coqc -I coq $<
coq/%_po_why.vo: coq/jessie-spaces-in--file--name_ctx_why.vo

pvs: pvs/jessie-spaces-in--file--name_why.pvs

pvs/%_why.pvs: WHYOPT=-pvs -dir pvs -pvs-preamble "IMPORTING why@jessie"
pvs/%_why.pvs: why/%.why
	$(WHY) $(JESSIELIBFILES) why/$*.why

pvs/jessie_why.pvs:WHYOPT=-pvs -dir pvs -pvs-preamble "IMPORTING why@why"
pvs/jessie_why.pvs:
	$(WHY) $(JESSIELIBFILES)

isabelle: isabelle/jessie-spaces-in--file--name_why.thy

isabelle/%_why.thy: WHYOPT=-isabelle -dir isabelle -isabelle-base-theory jessie_why
isabelle/%_why.thy: why/%.why
	$(WHY) $(JESSIELIBFILES) why/$*.why
	cp -f /home/mikhail/.opam/4.02.1/lib/why/isabelle/jessie_why.thy isabelle/

simplify: simplify/jessie-spaces-in--file--name_why.sx
	@echo 'Running Simplify on proof obligations' && ($(DP) $^)

simplify/%_why.sx: WHYOPT=-simplify -dir simplify
simplify/%_why.sx: why/%.why
	@echo 'why -simplify [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why

vampire: vampire/jessie-spaces-in--file--name_why.vp
	@echo 'Running Vampire on proof obligations' && ($(DP) $^)

vampire/%_why.vp: WHYOPT=-vampire -dir vampire
vampire/%_why.vp: why/%.why
	@echo 'why -vampire [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why

alt-ergo ergo: why/jessie-spaces-in--file--name_why.why
	@echo 'Running Alt-Ergo on proof obligations' && ($(DP) $^)

why/%_why.why: WHYOPT=-alt-ergo -dir why
why/%_why.why: why/%.why
	@echo 'why -alt-ergo [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why

gappa: gappa/jessie-spaces-in--file--name_why.gappa
	@echo 'Running Gappa on proof obligations' && ($(DP) $^)

gappa/%_why.gappa: WHYOPT=-gappa -dir gappa
gappa/%_why.gappa: why/%.why
	@echo 'why -gappa [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why

cvcl: cvcl/jessie-spaces-in--file--name_why.cvc

	@echo 'Running CVC Lite on proof obligations' && ($(DP) $^)

cvcl/%_why.cvc: WHYOPT=-cvcl -dir cvcl
cvcl/%_why.cvc: why/%.why
	@echo 'why -cvcl [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why

harvey: harvey/jessie-spaces-in--file--name_why.rv
	@echo 'Running haRVey on proof obligations' && ($(DP) $^)

harvey/%_why.rv: WHYOPT=-harvey -dir harvey
harvey/%_why.rv: why/%.why
	@echo 'why -harvey [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why

zenon: zenon/jessie-spaces-in--file--name_why.znn
	@echo 'Running Zenon on proof obligations' && ($(DP) $^)

zenon/%_why.znn: WHYOPT=-zenon -dir zenon
zenon/%_why.znn: why/%.why
	@echo 'why -zenon [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why

smtlib: smtlib/jessie-spaces-in--file--name_why.smt
	@echo 'Running Z3 on proof obligations' && ($(DP) $^)

smtlib/%_why.smt:  WHYOPT=-smtlib --encoding sstrat --exp goal -dir smtlib
smtlib/%_why.smt: why/%.why
	@echo 'why -smtlib [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why

z3: smtlib/jessie-spaces-in--file--name_why.smt
	@echo 'Running Z3 on proof obligations' && ($(DP) -smt-solver z3 $^)

yices: smtlib/jessie-spaces-in--file--name_why.smt
	@echo 'Running Yices on proof obligations' && ($(DP) -smt-solver yices $^)

cvc3: smtlib/jessie-spaces-in--file--name_why.smt
	@echo 'Running CVC3 on proof obligations' && ($(DP) -smt-solver cvc3 $^)

smtlib-v1: smtlib-v1/jessie-spaces-in--file--name_why.smt
smtlib-v1/%_why.smt:  WHYOPT=-smtlib --smtlib-v1 --encoding sstrat --exp goal -dir smtlib-v1
smtlib-v1/%_why.smt: why/%.why
	@echo 'why -smtlib [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why

verit: smtlib-v1/jessie-spaces-in--file--name_why.smt
	@echo 'Running VeriT on proof obligations' && ($(DP) -smt-solver verit $^)

gui stat: jessie-spaces-in--file--name.stat

%.stat: why/%.why
	@echo 'gwhy-bin [...] why/$*.why' && $(GWHY) $(JESSIELIBFILES) why/$*.why

why3: why/jessie-spaces-in--file--name_why3.why
why/%_why3.why:  WHYOPT=-why3
why/%_why3.why: why/%.why
	@echo 'why -why3 [...] why/$*.why' && $(WHY) $(JESSIELIBFILES) why/$*.why
why3ml: jessie-spaces-in--file--name.mlw
	 why3 $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<

why3ide: jessie-spaces-in--file--name.mlw
	 why3 ide $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<

why3replay: jessie-spaces-in--file--name.mlw
	 why3 replay $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<

why3autoreplay: jessie-spaces-in--file--name.mlw
	 why3 replay -q -f --obsolete-only $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<

-include jessie-spaces-in--file--name.depend

depend: coq/jessie-spaces-in--file--name_why.v
	-$(COQDEP) -I coq coq/jessie-spaces-in--file--name*_why.v > jessie-spaces-in--file--name.depend

clean:
	rm -f coq/*.vo

