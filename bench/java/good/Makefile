
JESSIE=ocamlrun -bt ../../../bin/jessie.byte
JESSIELIB=$(shell pwd)/../../../lib
WHYLIB=$(shell pwd)/../../../lib

EXECJESSIE=WHYLIB=$(WHYLIB) JESSIELIB=$(JESSIELIB) $(JESSIE) -why-opt -split-user-conj 

KRAKATOA=ocamlrun -bt ../../../bin/krakatoa.byte
KRAKATOALIB=$(shell pwd)/../../../lib

EXECKRAKATOA=KRAKATOALIB=$(KRAKATOALIB) $(KRAKATOA)
JAVAFILES=$(shell ls *.java)
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

%.jc: %.java 
	$(EXECKRAKATOA) $<

%.jcio: %.java 
	$(EXECKRAKATOA) -ignore-overflow $<

why/%.why: %.jc 
	$(EXECJESSIE) -locs $*.jloc $<

why/%.whyai: %.jc 
	$(EXECJESSIE) -ai pol -main main $<

simplify/%_why.sx.all: %.jc $(JESSIE) $(JESSIELIB)/why/jessie.why
	$(EXECJESSIE) $<
	make -f $*.makefile $@

smtlib/%_why.smt.all: %.jc $(JESSIE) $(JESSIELIB)/why/jessie.why
	$(EXECJESSIE) $<
	make -f $*.makefile $@

%: %.java
	rm -f $*.jc
	make $*.jc
	make why/$*.why
	make -f $*.makefile gui

%.io: %.java
	rm -f $*.jc
	make $*.jcio
	make why/$*.why
	make -f $*.makefile gui

%.ai: %.java
	rm -f $*.jc
	make $*.jcio
	make why/$*.whyai
	make -f $*.makefile gui

%.goals: %.jc
	mkdir -p why
	rm -f why/$*.why
	make why/$*.why
	make -f $*.makefile goals
	gwhy -no-prelude why/$*_why.why

%.coq: %.jc
	mkdir -p why
	rm -f why/$*.why
	make why/$*.why
	make -f $*.makefile coq

.PHONY: simplify coq harvey cvcl

clean:
	rm -f why/*.why coq/*.vo \
		coq/caduceus_why.v coq/caduceus_spec_why.v \
		simplify/*.sx
