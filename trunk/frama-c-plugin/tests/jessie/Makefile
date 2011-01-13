
# to run Frama-C with its Jessie plugin on a file toto.c, copy this Makefile
# in the same directory as the C file, set PPCHOME either in the Makefile or
# the environment, and call one of
# - "make toto", which calls the byte executables
# - "make toto.opt", which calls the opt executables
# Why should be installed for the regression tests to work.


#function canonpath ()
#{ echo $(cd $(dirname $1); pwd -P)/$(basename $1) }

PPCHOME:=$(shell (cd ../..; pwd -P))
WHYHOME:=$(shell (cd  ../../..; pwd -P))
FRAMAC_OPT:=$(shell ./check_opt.sh)
FRAMAC_BYTE?=OCAMLRUNPARAMS=-bt frama-c.byte 

JESSIEOPT=$(WHYHOME)/bin/jessie.opt
JESSIEBYTE=$(WHYHOME)/bin/jessie.byte
CADUCEUSOPT=$(WHYHOME)/bin/caduceus.opt
CADUCEUSBYTE=$(WHYHOME)/bin/caduceus.byte
WHYOPT=$(WHYHOME)/bin/why.opt
WHYBYTE=$(WHYHOME)/bin/why.byte
GWHYOPT=$(WHYHOME)/bin/gwhy.opt
GWHYBYTE=$(WHYHOME)/bin/gwhy.byte

CADUCEUSLIB=$(WHYHOME)/lib
WHYLIB=$(WHYHOME)/lib

ifneq ("$(FRAMAC_PLUGIN)","")
ifneq ("$(FRAMAC_PLUGIN)",".")
ENVPPC:=FRAMAC_PLUGIN=$(FRAMAC_PLUGIN)
else
ENVPPC:=FRAMAC_PLUGIN="`unset FRAMAC_PLUGIN; $(FRAMAC_BYTE) -print-plugin-path`"
endif
endif

ifeq ("$(wildcard $(PPCHOME)/Jessie.cma)","")
EXECPPCBYTE=$(ENVPPC) $(FRAMAC_BYTE)
else
EXECPPCBYTE=$(ENVPPC) $(FRAMAC_BYTE) -load-module $(PPCHOME)/Jessie.cma
endif

ifeq ($(FRAMAC_OPT),$(FRAMAC_BYTE))
EXECPPCOPT=$(EXECPPCBYTE)
else
ifeq ("$(wildcard $(PPCHOME)/Jessie.cmxs)","")
EXECPPCOPT=$(ENVPPC) $(FRAMAC_OPT)
else
EXECPPCOPT=$(ENVPPC) $(FRAMAC_OPT) -load-module $(PPCHOME)/Jessie.cmxs
endif
endif

EXECJESSIEOPT=WHYLIB=$(WHYLIB) $(JESSIEOPT)
EXECJESSIEBYTE=WHYLIB=$(WHYLIB) $(JESSIEBYTE)

ENVWHYOPT=WHYLIB=$(WHYLIB) WHYEXEC=$(WHYOPT) GWHYEXEC=$(GWHYOPT)
ENVWHYBYTE=WHYLIB=$(WHYLIB) WHYEXEC=$(WHYBYTE) GWHYEXEC=$(GWHYBYTE)

EXECCADUCEUSBYTE=WHYLIB=$(WHYLIB) CADUCEUSLIB=$(CADUCEUSLIB) $(CADUCEUSBYTE)
EXECCADUCEUSOPT=WHYLIB=$(WHYLIB) CADUCEUSLIB=$(CADUCEUSLIB) $(CADUCEUSOPT)

JC_OPTIONS+=-why-opt -split-user-conj
PPC_OPTIONS+=-cpp-extra-args="-I $(PPCHOME)/share/jessie" -jessie

DIR=`pwd`
CFILES=$(shell ls *.c)

# generating and type-checking Why files for all C files
default:
	for f in $(CFILES:.c=); do \
	  rm -f why/$$f.why $$f.jc; \
	  make $$f.jc; \
	  make why/$$f.why; \
	  make -f $$f.makefile simplify/$${f}_why.sx.all; \
	done
	dp -timeout 10 simplify/*_why.sx.all

%.jessie:
	$(EXECPPCBYTE) $(PPC_OPTIONS) -jessie-gen-only $*.c

%.why:
	cd $*.jessie; $(EXECJESSIEBYTE) $(JC_OPTIONS) -locs $*.cloc $*.jc

%.why.debug:
	cd $*.jessie; $(EXECJESSIEBYTE) $(JC_OPTIONS) -d -locs $*.cloc $*.jc

%: %.c
	rm -f $*.jessie/$*.jc
	echo $(FRAMAC_PLUGIN)
	echo $(FRAMAC_SHARE)
	$(EXECPPCBYTE) $(PPC_OPTIONS) -jessie-gen-only $^
	$(EXECJESSIEBYTE) $(JC_OPTIONS) -locs $*.jessie/$*.cloc $*.jessie/$*.jc
	$(ENVWHYOPT) make -C $*.jessie -f $*.makefile gui

%.coq: %.c
	rm -f $*.jessie/$*.jc
	$(EXECPPCBYTE) $(PPC_OPTIONS) -jessie-gen-only $^
	$(EXECJESSIEBYTE) $(JC_OPTIONS) -locs $*.jessie/$*.cloc $*.jessie/$*.jc
	$(ENVWHYOPT) make -C $*.jessie -f $*.makefile coq

arith: arith.c
	make arith.jc
	make why/arith.why
	make -C arith.jessie -f arith.makefile gui

%.nosep: %.c
	rm -rf $*.jessie
	PPC_OPTIONS="-jessie-no-regions $(PPC_OPTIONS)" make $*.jessie
	make $*.why
	cd $*.jessie; make -f $*.makefile gui

%.std: %.c
	rm -rf $*.jessie
	PPC_OPTIONS="-jessie-std-stubs $(PPC_OPTIONS)" make $*.jessie
	make $*.why
	cd $*.jessie; make -f $*.makefile gui

%.infer: %.c
	rm -rf $*.jessie
	PPC_OPTIONS="-jessie-infer-annot spre -jessie-abstract-domain oct \
		-jessie-hint-level 2 -jessie-int-model exact $(PPC_OPTIONS)" make $*.jessie
	make $*.why.debug
	cd $*.jessie; make -f $*.makefile gui

%.fastsep: %.c
	rm -rf $*.jessie
	$(EXECPPCBYTE) $(PPC_OPTIONS) -jessie-gen-only $^
	$(EXECJESSIEBYTE) -separation -why-opt -fast-wp $(JC_OPTIONS) -locs $*.jessie/$*.cloc $*.jessie/$*.jc
	$(ENVWHYOPT) make -C $*.jessie -f $*.makefile gui

%.opt: %.c
	rm -rf $*.jessie
	$(EXECPPCOPT) $(PPC_OPTIONS) -jessie-gen-only $^
	$(EXECJESSIEOPT) $(JC_OPTIONS) -locs $*.jessie/$*.cloc $*.jessie/$*.jc
	cd $*.jessie; $(ENVWHYOPT) make -f $*.makefile gui

%.fastwp: %.c
	rm -rf $*.jessie
	$(EXECPPCOPT) $(PPC_OPTIONS) -jessie-gen-only $^
	$(EXECJESSIEOPT) $(JC_OPTIONS) -locs $*.jessie/$*.cloc $*.jessie/$*.jc
	JC_OPTIONS="-why-opt -fast-wp $(JC_OPTIONS)" make $*.why
	cd $*.jessie; $(ENVWHYOPT) make -f $*.makefile gui

%.exact: %.c
	rm -rf $*.jessie
	PPC_OPTIONS="-jessie-int-model exact $(PPC_OPTIONS)" make $*.jc
	make $*.why
	cd $*.jessie; $(ENVWHYOPT) make -f $*.makefile gui

%.modulo: %.c
	rm -rf $*.jessie
	PPC_OPTIONS="-jessie-int-model modulo $(PPC_OPTIONS)" make $*.jc
	make $*.why
	cd $*.jessie; $(ENVWHYOPT) make -f $*.makefile gui

%.debug: %.c
	rm -f $*.jessie/$*.jc
	OCAMLRUNPARAM=bt $(EXECPPCBYTE) \
		-check -debug 1 \
		$(PPC_OPTIONS) -jessie-gen-only $^
# -files-debug -copy
	OCAMLRUNPARAM=bt $(EXECJESSIEBYTE) -d -locs $*.jessie/$*.cloc $*.jessie/$*.jc
	$(ENVWHYBYTE) make -C $*.jessie -f $*.makefile gui

%.cad: %.c
	rm -f $*.why
	rm -f coq/caduceus_spec_why.v
	$(EXECCADUCEUSOPT) -separation -why-opt -split-user-conj $<
	$(ENVWHYOPT) make -f $*.makefile gui

simplify/%_why.sx.all: %.c
	rm -f $*.jc
	make $*.jc
	make $*.why
	cd $*.jessie; $(ENVWHYOPT) make -f $*.makefile $@

# entries used by regression tests, do not modify without updating oracles

%.quick: %.c
	rm -rf $*.jessie
#	C to Jessie translation
	$(EXECPPCOPT) $(PPC_OPTIONS) -jessie-gen-only $^
#	Output Jessie file generated for diff in regression tests
	cat $*.jc

%.codegen: %.c
	rm -rf $*.jessie
#	C to Jessie translation
	$(EXECPPCOPT) $(PPC_OPTIONS) -jessie-gen-only $^
#	Jessie to Why translation
	$(EXECJESSIEOPT) $(JC_OPTIONS) -why-opt -fast-wp -locs $*.cloc $*.jc
#	Output Why file generated for diff in regression tests
	cat why/$*.why

%.regtest: %.c
	@rm -f $*.jessie/$*.jc
#	C to Jessie translation
	@echo "PPCHOME: $(PPCHOME)"
	@echo "PPCHOME: $(PPCHOME)" >&2
	@echo "WHYHOME: $(WHYHOME)"
	@echo "WHYHOME: $(WHYHOME)" >&2
	@echo "*** Begin output command for diff ***"
	@echo "*** Begin stderr for diff ***" >&2
	@echo Options are: $(PPC_OPTIONS) -jessie-gen-only $^
#	@echo "COMMAND=$(EXECPPCOPT)"
	@$(EXECPPCOPT) $(PPC_OPTIONS) -jessie-gen-only $^
	@echo "*** End output command for diff ***"
#	Output Jessie file generated for diff in regression tests
#	Following line is expected by [filter_output] to filter correctly
	@echo "*** Begin Jessie file generated for diff ***"
	@cat $*.jessie/$*.jc
	@echo "*** End Jessie file generated for diff ***"
#	Jessie to Why translation
	@rm -f $*.jessie/why/$*.why
	@echo "*** Begin output command for diff ***"
	@echo $(EXECJESSIEOPT) $(JC_OPTIONS) \
		-why-opt -fast-wp -locs $*.jessie/$*.cloc $*.jessie/$*.jc
	@echo "*** End output command for diff ***"
	@$(EXECJESSIEOPT) $(JC_OPTIONS) -why-opt -fast-wp \
		-locs $*.jessie/$*.cloc $*.jessie/$*.jc
#	Output Why file generated for diff in regression tests
	@echo "*** Begin Why file generated for diff ***"
	@cat $*.jessie/why/$*.why
	@echo "*** End Why file generated for diff ***"
#	VC generation
	@echo "*** Begin output command for diff ***"
	@echo $(ENVWHYOPT) make --quiet -C $*.jessie --quiet \
		-f $*.makefile project | sed -e "s|$(PPCHOME)|PPCHOME|g" | sed -e "s|$(WHYHOME)|WHYHOME|g"
	@echo "*** End output command for diff ***"
	@echo "*** Begin VC file generated for diff ***"
	@$(ENVWHYOPT) make --quiet -C $*.jessie -f $*.makefile project
	@cat $*.jessie/why/$*.wpr
	@cat $*.jessie/why/$*'_ctx'.why
	@for i in $(wildcard $*.jessie/why/$*'_po'*.why); do \
		cat $$i; \
	done
	@echo "*** End VC file generated for diff ***"
	@echo "*** End stderr for diff ***" >&2

%.ergo: %.c
	rm -rf $*.jessie
#	C to Jessie translation
	$(EXECPPCOPT) $(PPC_OPTIONS) -jessie-gen-only $^
#	Jessie to Why translation
	$(EXECJESSIEOPT) $(JC_OPTIONS) -why-opt -fast-wp -locs $*.jessie/$*.cloc $*.jessie/$*.jc
#	Prover ergo called
	$(ENVWHYOPT) make -C $*.jessie -f $*.makefile alt-ergo


clean:
	rm -f *.c~ *.o *.jc *.makefile *.loc
	rm -f gwhy.cache internal_dependencies.dot jessie.log
	rm -rf why
	rm -rf smtlib
