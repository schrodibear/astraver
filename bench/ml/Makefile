WHYDIR=../../
EXT=.opt
FASTWP=-why-opt --fast-wp
ALLVC=-why-opt --all-vc
SPLIT=-why-opt --split-user-conj
JESSIE=$(WHYDIR)bin/jessie$(EXT)
JESSICA=$(WHYDIR)bin/jessica$(EXT)

$(WHYDIR)%:
	make -j -C $(WHYDIR) $*

.SUFFIXES: .ml .jc .why

%.jc: %.ml $(JESSICA)
	$(JESSICA) pervasives.mli $*.ml

%.why: %.jc $(JESSIE)
	$(JESSIE) $(SPLIT) $*.jc

%: %.why
	make -f $*.makefile gui