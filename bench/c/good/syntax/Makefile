
CADUCEUS=../../../../bin/caduceus.opt 
CADUCEUSLIB=../../../../lib/why
EXECCADUCEUS=CADUCEUSLIB=$(CADUCEUSLIB) $(CADUCEUS)

all:
	export CADUCEUSLIB=../../../../lib/why; \
	for f in *.c; do \
	  $(CADUCEUS) -parse-only $$f; \
	done