
CADUCEUS=../../../bin/caduceus.opt
CADUCEUSLIB=$(shell pwd)/../../../lib
EXECCADUCEUS=CADUCEUSLIB=$(CADUCEUSLIB) $(CADUCEUS)

CFILES=$(shell ls *.c)
WFILES=$(addprefix why/, $(CFILES:.c=.why))

# generating and type-checking Why files for all C files
default:
	for f in $(CFILES:.c=); do \
	  rm -f why/$$f.why; \
	  make why/$$f.why; \
	  make -f $$f.makefile; \
	done

# running Simplify on all programs
# with log in simplify.log and statictics
simplify:
	time make clean do_simplify > simplify.log
	@echo -n "valid obligations: " 
	@egrep '[0-9]+: Valid.$$' simplify.log | wc -l
	@echo -n "invalid obligations: " 
	@egrep '[0-9]+: Invalid.$$' simplify.log | wc -l

# without log
do_simplify: $(WFILES)
	for f in $(CFILES:.c=); do \
	  rm -f why/$$f.why; \
	  make why/$$f.why; \
	  make -f $$f.makefile do_simplify; \
	done

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
	$(EXECCADUCEUS) -why-opt "-d -V" $<

%: %.c
	rm -f why/$*.why
	make why/$*.why
	make -f $*.makefile do_simplify

.PHONY: simplify coq

clean:
	rm -f why/*.why coq/*.vo \
		coq/caduceus_why.v coq/caduceus_spec_why.v \
		simplify/*.sx
