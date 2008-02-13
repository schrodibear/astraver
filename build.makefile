# This Makefile compiles the Why platform using Ocamlbuild.

ifeq ($(EMACS), yes)
  OCAMLBUILD=ocamlbuild -build-dir bin -no-hygiene -classic-display
else
  OCAMLBUILD=ocamlbuild -build-dir bin -no-hygiene
endif

# Binaries of the Why platform (with no extension)
WHY=why
JESSIE=jessie
KRAKATOA=krakatoa
JESSICA=jessica
CADUCEUS=caduceus

BYTES=$(WHY).byte $(JESSIE).byte $(KRAKATOA).byte $(JESSICA).byte \
	$(CADUCEUS).byte
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