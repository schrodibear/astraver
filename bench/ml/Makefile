WHYDIR=../../
EXT=.opt
JESSIE=$(WHYDIR)bin/jessie$(EXT)
JESSICA=$(WHYDIR)bin/jessica$(EXT)

TMPDIR=tmp

FASTWP=-why-opt --fast-wp
ALLVC=-why-opt --all-vc
SPLIT=-why-opt --split-user-conj

# Special, preferred targets:
# %.bench, ex: good.bench, to test all files in directory "good"
# %.gui, ex: max.gui, to test the file "good/max.ml" with gWhy
#   (the file must be in the "good" directory)
# %.coq, same but for Coq

$(WHYDIR)%.force:
	make -j -C $(WHYDIR) $*

%.gui: good/%.ml $(JESSICA).force $(JESSIE).force
	./test-gui.sh $*

%.coq: good/%.ml $(JESSICA).force $(JESSIE).force
	./test-coq.sh $*

%.bench-file:
	../bench.sh $*

bench-start: *.ml
	@echo "\n==============================================================\
=================="
	make -j -s -f ../Makefile $(^:.ml=.bench-file)

%.bench: $(JESSICA).force $(JESSIE).force
	rm -rf $(TMPDIR)
	mkdir -p $(TMPDIR)
	cp $*/*.ml $(TMPDIR)
	make -s -C $(TMPDIR) -f ../Makefile bench-start

retry:
	make -s -C $(TMPDIR) -f ../Makefile bench-start

clean:
	rm -rf $(TMPDIR)
	rm -f good/*.makefile
	rm -f good/*.jc
	rm -rf good/why
	rm -f good/*.log
	rm -f *.log
	rm -rf why
	rm -f *.loc