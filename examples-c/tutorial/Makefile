
FILES = max abs swap search purse average

coq:
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

%: %.c 
	caduceus $*.c
	make -f $*.makefile simplify
	make -f $*.makefile coq

clean:
	make -f purse.makefile clean
	make -f abs.makefile clean
	rm -f why/*.why
