CADUCEUS=../../bin/caduceus.opt 
CADUCEUSLIB=../../lib
EXECCADUCEUS=CADUCEUSLIB=$(CADUCEUSLIB) $(CADUCEUS)

test:
	-gcc -ansi -pedantic -Wall -c test.c
	$(EXECCADUCEUS) -v -type-only test.c

gcc:
	gcc -Wall test.c && ./a.out

test.i: test.c
	gcc -E $^ > $@

caduceus.why %.why: %.c $(CADUCEUS)
	$(EXECCADUCEUS) -v $<

WHY=../../bin/why.opt

%_why.v %_valid.v: %.why $(WHY)
	$(WHY) --valid -V --coq-v8 --coq-preamble "Require Export Why" caduceus.why $<

%_why.sx: %.why $(WHY)
	$(WHY) -V --simplify --no-simplify-prelude caduceus.why $<

%_why.pvs: %.why $(WHY)
	$(WHY) -V --pvs caduceus.why $<

%.sxcheck: %.sx
	cat caduceus_why.sx $< > $<.all
	Simplify $<.all

caduceus_why.v: caduceus.why $(WHY)
	$(WHY) --coq-v8 caduceus.why
