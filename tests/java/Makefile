
# to run Frama-C with its Jessie plugin on a file toto.c, copy this Makefile
# in the same directory as the C file, set PPCHOME either in the Makefile or
# the environment, and call one of
# - "make toto", which calls the byte executables
# - "make toto.opt", which calls the opt executables
# Why should be installed for the regression tests to work.


#function canonpath ()
#{ echo $(cd $(dirname $1); pwd -P)/$(basename $1) }

WHYHOME:=$(shell (cd  ../..; pwd -P))
KRAKATOAOPT=$(WHYHOME)/bin/krakatoa.opt
KRAKATOABYTE=$(WHYHOME)/bin/krakatoa.byte
JESSIEOPT=$(WHYHOME)/bin/jessie.opt
JESSIEBYTE=$(WHYHOME)/bin/jessie.byte
WHYOPT=$(WHYHOME)/bin/why.opt
WHYBYTE=$(WHYHOME)/bin/why.byte
GWHYOPT=$(WHYHOME)/bin/gwhy.opt
GWHYBYTE=$(WHYHOME)/bin/gwhy.byte

WHYLIB=$(WHYHOME)/lib

EXECKRAKATOAOPT=WHYLIB=$(WHYLIB) $(KRAKATOAOPT)
EXECKRAKATOABYTE=WHYLIB=$(WHYLIB) $(KRAKATOABYTE)
EXECJESSIEOPT=WHYLIB=$(WHYLIB) $(JESSIEOPT)
EXECJESSIEBYTE=WHYLIB=$(WHYLIB) $(JESSIEBYTE)

ENVWHYOPT=WHYLIB=$(WHYLIB) WHYEXEC=$(WHYOPT) GWHYEXEC=$(GWHYOPT)
ENVWHYBYTE=WHYLIB=$(WHYLIB) WHYEXEC=$(WHYBYTE) GWHYEXEC=$(GWHYBYTE)

JC_OPTIONS+=-why-opt -split-user-conj
KRAK_OPTIONS+=-gen-only

DIR=`pwd`
JAVAFILES=$(shell ls *.java)

# generating and type-checking Why files for all JAva files
default:
	for f in $(JAVAFILES:.java=); do \
	  rm -f why/$$f.why $$f.jc; \
	  make $$f.jc; \
	  make why/$$f.why; \
	  make -f $$f.makefile simplify/$${f}_why.sx.all; \
	done
	dp -timeout 10 simplify/*_why.sx.all

%.jessie:
	$(EXECKRAKATOABYTE) $(KRAK_OPTIONS) $*.java

%.why:
	$(EXECJESSIEBYTE) $(JC_OPTIONS) -locs $*.jloc $*.jc

%.gwhy: %.java
	rm -f $*.jc
	$(EXECKRAKATOABYTE) $(KRAK_OPTIONS) $^
	$(EXECJESSIEBYTE) $(JC_OPTIONS) -locs $*.jloc $*.jc
	$(ENVWHYOPT) make -f $*.makefile gui

%.why3ml: %.java
	rm -f $*.jc
	$(EXECKRAKATOABYTE) $(KRAK_OPTIONS) $^
	$(EXECJESSIEBYTE) -why3ml $(JC_OPTIONS) -locs $*.jloc $*.jc
	$(ENVWHYOPT) make -f $*.makefile why3ml

%.coq: %.java
	rm -f $*.jc
	$(EXECKRAKATOABYTE) $(KRAK_OPTIONS) $^
	$(EXECJESSIEBYTE) $(JC_OPTIONS) -locs $*.jloc $*.jc
	$(ENVWHYOPT) make -f $*.makefile coq

clean:
	rm -f *.java~ *.o *.jc *.makefile *.loc *.jloc
	rm -f gwhy.cache internal_dependencies.dot jessie.log
	rm -rf why
	rm -rf smtlib
