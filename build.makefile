# This Makefile compiles the Why platform using Ocamlbuild.

OCAMLBUILD1=ocamlbuild

ifeq ($(EMACS), yes)
  OCAMLBUILD2=$(OCAMLBUILD1) -classic-display
else
  OCAMLBUILD2=$(OCAMLBUILD1)
endif

ifeq ($(VERBOSE), yes)
  OCAMLBUILD3=$(OCAMLBUILD2) -verbose 10
else
  OCAMLBUILD3=$(OCAMLBUILD2)
endif

OCAMLBUILD=$(OCAMLBUILD3)

# Binaries of the Why platform (with no extension)
WHY=why
JESSIE=jessie
KRAKATOA=krakatoa
JESSICA=jessica
CADUCEUS=caduceus
WHY2HTML=why2html
DP=dp
RV_MERGE=rv_merge
WHY_OBFUSCATOR=why-obfuscator
SIMPLIFY2WHY=simplify2why
WHY_STAT=why-stat
DEMIXIFY=demixify
GWHY=gwhy

BYTES=$(WHY).byte $(JESSIE).byte $(KRAKATOA).byte $(JESSICA).byte \
	$(CADUCEUS).byte $(WHY2HTML).byte $(DP).byte $(RV_MERGE).byte \
	$(WHY_OBFUSCATOR).byte $(SIMPLIFY2WHY).byte $(WHY_STAT).byte \
	$(DEMIXIFY).byte $(GWHY).byte

OPTS=$(BYTES:.byte=.opt)

# Default target

all:
	$(OCAMLBUILD) $(BYTES) $(OPTS)

# Other useful targets

byte:
	$(OCAMLBUILD) $(BYTES)

opt:
	$(OCAMLBUILD) $(OPTS)

%.all:
	$(OCAMLBUILD) $*.byte $*.opt

%.byte:
	$(OCAMLBUILD) $*.byte

%.opt:
	$(OCAMLBUILD) $*.opt

%.cmo:
	$(OCAMLBUILD) $*.cmo

%.cmi:
	$(OCAMLBUILD) $*.cmi

# Bench

ml-bench:
	$(OCAMLBUILD) $(JESSICA).opt $(JESSIE).opt $(WHY).opt
	make -C bench/ml good.bench

ml-bench-retry:
	$(OCAMLBUILD) $(JESSICA).opt $(JESSIE).opt $(WHY).opt
	make -C bench/ml retry

jc-bench:
	$(OCAMLBUILD) $(JESSIE).opt $(WHY).opt
	make -C bench/jc good.bench

jc-bench-retry:
	$(OCAMLBUILD) $(JESSIE).opt $(WHY).opt
	make -C bench/jc retry

# Cleaning

clean:
	$(OCAMLBUILD) -clean