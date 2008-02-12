# This Makefile compiles the Why platform using Ocamlbuild.

OCAMLBUILD=ocamlbuild -build-dir bin -no-hygiene

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

# Cleaning

clean:
	$(OCAMLBUILD) -clean