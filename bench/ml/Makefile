WHYDIR=../../
BINDIR=$(WHYDIR)bin/
JESSIE=$(BINDIR)jessie
JESSICA=$(BINDIR)jessica

TMPDIR=tmp

FASTWP=-why-opt --fast-wp
ALLVC=-why-opt --all-vc
SPLIT=-why-opt --split-user-conj

default: good.bench

# Special, preferred targets:
# %.bench, ex: good.bench, to test all files in directory "good"
# %.gui, ex: max.gui, to test the file "good/max.ml" with gWhy
#   (the file must be in the "good" directory)
# %.coq, same but for Coq

%.gui:
	./test-gui.sh $*

%.coq:
	./test-coq.sh $*

%.bench-file:
	../bench.sh $*

bench-start: *.ml
	@echo "\n==============================================================\
=================="
	make -j -s -f ../Makefile $(^:.ml=.bench-file)

%.bench:
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
	rm -f *~
	rm -f good/*~