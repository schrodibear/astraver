
FILES = max abs swap search purse 

coq:
	for f in $(FILES); do \
	  caduceus $$f.c; \
	  make -f $$f.makefile coq; \
	done

simplify:
	for f in $(FILES); do \
	  caduceus $$f.c; \
	  make -f $$f.makefile simplify; \
	done

.PHONY: coq simplify

%: %.c 
	caduceus $*.c
	make -f $*.makefile simplify
	make -f $*.makefile coq

clean:
	make -f purse.makefile clean
	make -f abs.makefile clean
	rm -f why/*.why
