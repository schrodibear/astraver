
CADUCEUS=../../bin/caduceus.opt
CADUCEUSLIB=$(shell pwd)/../../lib
EXECCADUCEUS=CADUCEUSLIB=$(CADUCEUSLIB) $(CADUCEUS)

FILES = max abs swap search purse 

TODO = average

coq: $(FILES)

allcoq:
	for f in $(FILES); do \
	  caduceus $$f.c; \
	  rm -f coq/caduceus_spec_why.v; \
	  make -f $$f.makefile coq; \
	done

simplify:
	for f in $(FILES); do \
	  caduceus $$f.c; \
	  make -f $$f.makefile simplify; \
	done

cvcl:
	for f in $(FILES); do \
	  caduceus $$f.c; \
	  make -f $$f.makefile cvcl; \
	done

.PHONY: coq simplify cvcl

why/%.why: %.c 
	rm -f coq/caduceus_spec_why.v
	$(EXECCADUCEUS) $<

%: %.c
	rm -f why/$*.why
	make why/$*.why
	make -f $*.makefile coq


clean:
	for f in $(FILES); do make -f $$f.makefile clean
	rm -f why/*.why
