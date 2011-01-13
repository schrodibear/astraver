WHYDIR=../../
EXT=.opt
JESSIE=WHYLIB=$(WHYDIR)/lib $(WHYDIR)bin/jessie$(EXT)

TMPDIR=tmp

FASTWP=-why-opt --fast-wp
ALLVC=-why-opt --all-vc
SPLIT=-why-opt --split-user-conj

# Special, preferred targets:
# %.bench, ex: good.bench, to test all files in directory "good"

%.bench-file:
	../bench.sh $*

bench-start: *.jc
	@echo "\n==============================================================\
=================="
	make -j -s -f ../Makefile $(^:.jc=.bench-file)

%.bench:
	rm -rf $(TMPDIR)
	mkdir -p $(TMPDIR)
	cp $*/*.jc $(TMPDIR)
	make -s -C $(TMPDIR) -f ../Makefile bench-start

retry:
	make -s -C $(TMPDIR) -f ../Makefile bench-start

clean:
	rm -rf $(TMPDIR)
	rm -f *.log
	rm -rf why
	rm -f *.loc
	rm -f *~