
CADUCEUS=../../../bin/caduceus.opt
CADUCEUSLIB=$(shell pwd)/../../../lib
WHYLIB=$(shell pwd)/../../../lib
EXECCADUCEUS=WHYLIB=$(WHYLIB) CADUCEUSLIB=$(CADUCEUSLIB) $(CADUCEUS) -v -print-norm -separation -why-opt -split-user-conj

CFILES=$(shell ls *.c)
WFILES=$(addprefix why/, $(CFILES:.c=.why))

BENCHFILES=$(shell cat ../bench-files)
CBENCHFILES=$(addsuffix .c, $(BENCHFILES))
WBENCHFILES=$(addprefix why/, $(CBENCHFILES:.c=.why))
SBENCHFILES=$(addprefix simplify/, $(CBENCHFILES:.c=_why.sx.all))
HBENCHFILES=$(addprefix harvey/, $(CBENCHFILES:.c=_why.all.rv))

TIMEOUT=60

# generating and type-checking Why files for all C files
default:
	for f in $(CFILES:.c=); do \
	  rm -f why/$$f.why; \
	  make why/$$f.why; \
	  make -f $$f.makefile simplify/$${f}_why.sx.all; \
	  make -f $$f.makefile cvcl/$${f}_why.cvc.all; \
	done
	dp -timeout 10 simplify/*_why.sx.all
	dp -timeout 10 cvcl/*_why.cvc.all

# running Simplify on all programs
simplify: $(SBENCHFILES)
	dp -timeout $(TIMEOUT) $(SBENCHFILES)

# running haRVey on all programs
harvey: $(HBENCHFILES)
	dp -timeout $(TIMEOUT) $(HBENCHFILES)

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
	export CADUCEUSLIB=../../../lib/why; \
	for f in *.c; do \
	  $(CADUCEUS) -type-only $$f; \
	done

# rules ##################################################

why/%.why: %.c $(CADUCEUS) $(CADUCEUSLIB)/why/caduceus.why
	rm -f coq/caduceus_spec_why.v
	$(EXECCADUCEUS) $<

why/init2.why: init2.c $(CADUCEUS) $(CADUCEUSLIB)/why/caduceus.why
	rm -f coq/caduceus_spec_why.v
	$(EXECCADUCEUS) -closed $<

simplify/%_why.sx.all: %.c $(CADUCEUS) $(CADUCEUSLIB)/why/caduceus.why
	rm -f coq/caduceus_spec_why.v
	$(EXECCADUCEUS) $<
	make -f $*.makefile $@

harvey/%_why.all.rv: %.c $(CADUCEUS) $(CADUCEUSLIB)/why/caduceus.why
	rm -f coq/caduceus_spec_why.v
	$(EXECCADUCEUS) $<
	make -f $*.makefile $@

%: %.c
	rm -f why/$*.why
	make why/$*.why
	make -f $*.makefile simplify

%.gui: %.c
	rm -f why/$*.why
	make why/$*.why
	make -f $*.makefile gui

%.coq: %.c
	rm -f why/$*.why
	make why/$*.why
	make -f $*.makefile coq

%.overflow: %.c
	rm -f why/$*.why
	$(EXECCADUCEUS) --int-overflow $<
	make -f $*.makefile gui

.PHONY: simplify coq harvey cvcl

clean:
	rm -f why/*.why coq/*.vo \
		coq/caduceus_why.v coq/caduceus_spec_why.v \
		simplify/*.sx
