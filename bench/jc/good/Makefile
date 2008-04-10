
JESSIE=ocamlrun -bt ../../../bin/jessie.byte
#JESSIE=../../../bin/jessie.byte
JESSIELIB=$(shell pwd)/../../../lib
WHYLIB=$(shell pwd)/../../../lib

EXECJESSIE=WHYLIB=$(WHYLIB) JESSIELIB=$(JESSIELIB) $(JESSIE) -why-opt -split-user-conj

JCFILES=$(shell ls *.jc)
WFILES=$(addprefix why/, $(JCFILES:.jc=.why))

TIMEOUT=60

# generating and type-checking Why files for all JC files
default:
	for f in $(JCFILES:.jc=); do \
	  rm -f why/$$f.why; \
	  make why/$$f.why; \
	  make -f $$f.makefile simplify/$${f}_why.sx.all; \
	done
	dp -timeout 10 simplify/*_why.sx.all

# running Simplify on all programs
simplify: $(SBENCHFILES)
	dp -timeout $(TIMEOUT) $(SBENCHFILES)

# running yices/rvsat on all programs
smtlib: $(SMTBENCHFILES)
	dp -timeout $(TIMEOUT) $(SMTBENCHFILES)

# running haRVey on all programs
harvey: $(HBENCHFILES)
	dp -timeout $(TIMEOUT) $(HBENCHFILES)

# running cvcl on all programs
cvcl: $(CVCBENCHFILES)
	for f in $(BENCHFILES); do \
	  rm -f why/$$f.why; \
	  make why/$$f.why; \
	  make -f $$f.makefile cvcl/$${f}_why.cvc.all; \
	done
	dp -timeout 10 cvcl/*_why.cvc.all

# running Coq on all programs
coq:
	for f in $(BENCHFILES); do \
	  rm -f why/$$f.why; \
	  make why/$$f.why; \
	  make -f $$f.makefile coq || exit 1; \
	done

# type-checking all C programs
type-all:
	export JESSIELIB=../../../lib/why; \
	for f in *.jc; do \
	  $(JESSIE) -type-only $$f; \
	done

# rules ##################################################

$(JESSIE):
	make -C ../../.. bin/jessie.byte

why/%.why: %.jc $(JESSIE) $(JESSIELIB)/why/jessie.why
	$(EXECJESSIE) $<

simplify/%_why.sx.all: %.jc $(JESSIE) $(JESSIELIB)/why/jessie.why
	$(EXECJESSIE) $<
	make -f $*.makefile $@

smtlib/%_why.smt.all: %.jc $(JESSIE) $(JESSIELIB)/why/jessie.why
	$(EXECJESSIE) $<
	make -f $*.makefile $@

%: %.jc
	mkdir -p why
	rm -f why/$*.why
	rm -f why/$*.xpl
	make why/$*.why
	make -f $*.makefile gui

%.split: %.jc
	mkdir -p why
	rm -f why/$*.why
	rm -f why/$*.xpl
	$(EXECJESSIE) -why-opt -split-user-conj $<
	make -f $*.makefile gui

%.goals: %.jc
	mkdir -p why
	rm -f why/$*_ctx.why why/$*_po*.why 
	rm -f why/$*_po*.xpl
	make why/$*.why
	make -f $*.makefile goals

%.coq: %.jc
	mkdir -p why
	rm -f why/$*.why
	make why/$*.why
	make -f $*.makefile goals
	make -f $*.makefile coq/$*_ctx_why.vo
	for f in why/$*_po*.why; do make -f $*.makefile coq/`basename $$f .why`_why.v ; done

%.ergo: %.jc
	mkdir -p why
	rm -f why/$*.why
	make why/$*.why
	make -f $*.makefile ergo

.PHONY: simplify coq harvey cvcl

clean:
	rm -f why/*.why coq/*.vo \
		coq/caduceus_why.v coq/caduceus_spec_why.v \
		simplify/*.sx
