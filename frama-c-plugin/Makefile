##########################################################################
#                                                                        #
#  This file is part of Frama-C.                                         #
#                                                                        #
#  Copyright (C) 2007-2009                                               #
#    INRIA (Institut National de Recherche en Informatique et en         #
#           Automatique)                                                 #
#                                                                        #
#  you can redistribute it and/or modify it under the terms of the GNU   #
#  Lesser General Public License as published by the Free Software       #
#  Foundation, version 2.1.                                              #
#                                                                        #
#  It is distributed in the hope that it will be useful,                 #
#  but WITHOUT ANY WARRANTY; without even the implied warranty of        #
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         #
#  GNU Lesser General Public License for more details.                   #
#                                                                        #
#  See the GNU Lesser General Public License version 2.1                 #
#  for more details (enclosed in the file licenses/LGPLv2.1).            #
#                                                                        #
##########################################################################

# Makefile for compiling Jessie independently of Frama-C.
#
# To be used independently of Frama-C, a version of Frama-C compatible with
# Jessie has to be properly installed as long as the Jessie-specific stuff.

# Do not use ?= to initialize both below variables
# (fixed efficiency issue, see GNU Make manual, Section 8.11)
ifndef FRAMAC_SHARE
FRAMAC_SHARE  :=$(shell frama-c -journal-disable -print-path)
endif
ifndef FRAMAC_LIBDIR
FRAMAC_LIBDIR :=$(shell frama-c -journal-disable -print-libpath)
endif

WHY_DISTRIB	?= ..
JESSIE_INCLUDES	?= -I $(WHY_DISTRIB)/src -I $(WHY_DISTRIB)/jc
JCCMO		?= $(WHY_DISTRIB)/jc/jc.cmo
JCCMX		?= $(JCCMO:.cmo=.cmx)
PLUGIN_DIR      ?=.

PLUGIN_NAME:=Jessie
PLUGIN_CMO:= jessie_config jessie_options integer common rewrite \
             norm retype interp register
PLUGIN_HAS_MLI:=yes
PLUGIN_BFLAGS:=$(JESSIE_INCLUDES)
PLUGIN_OFLAGS:=$(JESSIE_INCLUDES)
PLUGIN_EXTRA_BYTE+=$(JCCMO)
PLUGIN_EXTRA_OPT+=$(JCCMX)
PLUGIN_DEPFLAGS:=$(JESSIE_INCLUDES)
PLUGIN_DOCFLAGS:=$(JESSIE_INCLUDES)

PLUGIN_TESTS_DIRS:=jessie

interp.cmo: $(WHY_DISTRIB)/jc/jc.cmo

interp.cmi: $(WHY_DISTRIB)/jc/jc.cmi

interp.cmx: $(WHY_DISTRIB)/jc/jc.cmx


ifeq ($(FRAMAC_MAKE),yes)
unexport $(FRAMAC_MAKE)

all: why_all

.PHONY: why_all
why_all: all: $(WHY_DISTRIB)/Makefile
	$(MAKE) -C $(WHY_DISTRIB) all

depend::
	$(MAKE) -C $(WHY_DISTRIB) depend

clean::
	$(MAKE) -C $(WHY_DISTRIB) clean
endif

jessie_config.ml:
	echo "let jessie_local = false" > $@

$(WHY_DISTRIB)/Makefile: $(WHY_DISTRIB)/Makefile.in $(WHY_DISTRIB)/config.status
	cd $(WHY_DISTRIB) && ./config.status

$(WHY_DISTRIB)/config.status: $(WHY_DISTRIB)/configure
	cd $(WHY_DISTRIB) && ./config.status --recheck

$(WHY_DISTRIB)/configure: $(WHY_DISTRIB)/configure.in
	cd $(WHY_DISTRIB) && autoconf

$(WHY_DISTRIB)/%:
	$(MAKE) -C $(WHY_DISTRIB) $*

PLUGIN_GENERATED_LIST+=$(JESSIE_HOME_DIR)/jessie_config.ml

include $(FRAMAC_SHARE)/Makefile.dynamic

tests: $(WHY_DISTRIB)/bin/jessie.$(OCAMLBEST) $(WHY_DISTRIB)/bin/why.$(OCAMLBEST)
