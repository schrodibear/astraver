
CADUCEUS=../../../bin/caduceus.opt
CADUCEUSLIB=$(shell pwd)/../../../lib
EXECCADUCEUS=CADUCEUSLIB=$(CADUCEUSLIB) $(CADUCEUS) -v # -print-norm

CFILES=$(shell ls *.c)
WFILES=$(addprefix why/, $(CFILES:.c=.why))

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
simplify: $(WFILES)
	for f in $(CFILES:.c=); do \
	  rm -f why/$$f.why; \
	  make why/$$f.why; \
	  make -f $$f.makefile simplify/$${f}_why.sx.all; \
	done
	dp -timeout 10 simplify/*_why.sx.all

cvcl: $(CFILES)
	for f in $(CFILES:.c=); do \
	  rm -f why/$$f.why; \
	  make why/$$f.why; \
	  make -f $$f.makefile cvcl/$${f}_why.cvc.all; \
	done
	dp -timeout 10 cvcl/*_why.cvc.all

# running Coq on all programs
coq: $(WFILES)
	for f in $(CFILES:.c=); do \
	  rm -f why/$$f.why; \
	  make why/$$f.why; \
	  make -f $$f.makefile coq; \
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

%: %.c
	rm -f why/$*.why
	make why/$*.why
	make -f $*.makefile simplify

.PHONY: simplify coq

clean:
	rm -f why/*.why coq/*.vo \
		coq/caduceus_why.v coq/caduceus_spec_why.v \
		simplify/*.sx
