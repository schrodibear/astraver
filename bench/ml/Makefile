WHYDIR=../../
EXT=.opt
FASTWP=-why-opt --fast-wp
ALLVC=-why-opt --all-vc
JESSIE=$(WHYDIR)bin/jessie$(EXT)
JESSICA=$(WHYDIR)bin/jessica$(EXT)

$(WHYDIR)%:
	make -j -C $(WHYDIR) $*

.SUFFIXES: .ml .jc .why

%.jc: %.ml $(JESSICA)
	$(JESSICA) pervasives.mli $*.ml

%.why: %.jc $(JESSIE)
	$(JESSIE) $*.jc

%: %.why
	make -f $*.makefile gui