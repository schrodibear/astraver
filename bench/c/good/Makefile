
CADUCEUS=../../../bin/caduceus.opt 
CADUCEUSLIB=$(shell pwd)/../../../lib
EXECCADUCEUS=CADUCEUSLIB=$(CADUCEUSLIB) $(CADUCEUS)

CFILES=$(shell ls *.c)
WFILES=$(addprefix why/, $(CFILES:.c=.why))

all:
	echo $(CADUCEUSLIB)

why/%.why: %.c $(CADUCEUS) $(CADUCEUSLIB)/why/caduceus.why
	$(EXECCADUCEUS) $<

%: %.c
	rm -f why/$*.why
	make why/$*.why
	make -f $*.makefile do_simplify

.PHONY: simplify coq

simplify:
	time make clean do_simplify > simplify.log
	@echo -n "valid obligations: " 
	@egrep '[0-9]+: Valid.$$' simplify.log | wc -l
	@echo -n "invalid obligations: " 
	@egrep '[0-9]+: Invalid.$$' simplify.log | wc -l

do_simplify: $(WFILES)
	for f in $(CFILES:.c=); do \
	  rm -f why/$$f.why; \
	  make why/$$f.why; \
	  make -f $$f.makefile do_simplify; \
	done

coq: $(WFILES)
	for f in $(CFILES:.c=); do \
	  rm -f why/$$f.why; \
	  make why/$$f.why; \
	  make -f $$f.makefile coq; \
	done

type-all:
	export CADUCEUSLIB=../../../lib/why; \
	for f in *.c; do \
	  $(CADUCEUS) -type-only $$f; \
	done

clean:
	rm -f why/*.why coq/*.vo \
		coq/caduceus_why.v coq/caduceus_spec_why.v \
		simplify/*.sx
