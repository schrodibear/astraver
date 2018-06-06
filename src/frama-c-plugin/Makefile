##########################################################################
#                                                                        #
#  This file is part of Frama-C.                                         #
#                                                                        #
#  Copyright (C) 2007-2010                                               #
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
# Jessie has to be properly installed as well as the Jessie-specific stuff.

# Do not use ?= to initialize both below variables
# (fixed efficiency issue, see GNU Make manual, Section 8.11)
ifndef FRAMAC_SHARE
FRAMAC_SHARE  :=$(shell $(FRAMAC) -journal-disable -print-path)
endif
ifndef FRAMAC_LIBDIR
FRAMAC_LIBDIR :=$(shell $(FRAMAC) -journal-disable -print-libpath)
endif

NUMS_DIR :=$(shell ocamlfind query num.core)

PLUGIN_DIR      ?= .
WHY_DISTRIB	?= $(PLUGIN_DIR)/../..
BUILDSRC        ?= $(WHY_DISTRIB)/_build/src
JESSIE_INCLUDES	?= -I $(BUILDSRC)/why -I $(BUILDSRC)/jc
JCCMA		?= $(BUILDSRC)/jc/jc.cma
JCCMXA		?= $(JCCMA:.cma=.cmxa)

PLUGIN_NAME:=Jessie
PLUGIN_CMO:= jessie_options jessie_integer common extractor rewrite \
             retype norm interp register
PLUGIN_HAS_MLI:=yes
PLUGIN_BFLAGS:=$(JESSIE_INCLUDES) -w -48 -safe-string -short-paths -strict-formats -no-alias-deps
PLUGIN_OFLAGS:=$(JESSIE_INCLUDES) -w -48 -safe-string -short-paths -strict-formats -no-alias-deps
PLUGIN_EXTRA_BYTE+=$(NUMS_DIR)/nums.cma $(JCCMA)
PLUGIN_EXTRA_OPT+=$(NUMS_DIR)/nums.cmxa $(JCCMXA)
PLUGIN_DOCFLAGS:=$(JESSIE_INCLUDES)
PLUGIN_TESTS_DIRS:=jessie

ifeq ($(FRAMAC_MAKE),yes)
unexport $(FRAMAC_MAKE)
endif

$(PLUGIN_DIR)/interp.cmo: $(PLUGIN_DIR)/interp.cmi $(JCCMA)

$(PLUGIN_DIR)/interp.cmi: $(BUILDSRC)/jc/jc.cmi

$(PLUGIN_DIR)/interp.cmx: $(PLUGIN_DIR)/interp.cmi $(JCCMXA)

RESOURCES   ?= jessie_spec_prolog.h

install::
	$(MKDIR) $(FRAMAC_DATADIR)/jessie
	$(CP) $(addprefix $(PLUGIN_DIR)/share/jessie/,$(RESOURCES)) $(FRAMAC_DATADIR)/jessie

uninstall::
	$(RM) -r $(FRAMAC_DATADIR)/jessie

include $(FRAMAC_SHARE)/Makefile.dynamic
