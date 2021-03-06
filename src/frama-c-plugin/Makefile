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

# Makefile for compiling AstraVer

# Do not use ?= to initialize both below variables
# (fixed efficiency issue, see GNU Make manual, Section 8.11)
ifndef FRAMAC_SHARE
FRAMAC_SHARE  :=$(shell $(FRAMAC) -journal-disable -print-path)
endif
ifndef FRAMAC_LIBDIR
FRAMAC_LIBDIR :=$(shell $(FRAMAC) -journal-disable -print-libpath)
endif

NUMS_DIR :=$(shell ocamlfind query num.core)
ASTRAVER_DIR :=$(shell ocamlfind query astraver)

PLUGIN_DIR      ?= .
AV_DISTRIB	?= $(PLUGIN_DIR)/../..
BUILDSRC        ?= $(AV_DISTRIB)/_build/default/src
AV_INCLUDES	?= -I $(NUMS_DIR)
AV_PKGS		?= -package astraver

PLUGIN_NAME:=AstraVer_plugin
PLUGIN_CMO:= astraver_options astraver_integer common extractor rewrite \
             retype norm interp register
PLUGIN_HAS_MLI:=yes
PLUGIN_DEPENDENCIES:=Variadic
PLUGIN_BFLAGS:=$(AV_PKGS) $(AV_INCLUDES) -w -48 -safe-string -short-paths -strict-formats -no-alias-deps
PLUGIN_OFLAGS:=$(AV_PKGS) $(AV_INCLUDES) -w -48 -safe-string -short-paths -strict-formats -no-alias-deps
PLUGIN_EXTRA_BYTE+=$(NUMS_DIR)/nums.cma $(ASTRAVER_DIR)/astraver.cma
PLUGIN_EXTRA_OPT+=$(NUMS_DIR)/nums.cmxa $(ASTRAVER_DIR)/astraver.cmxa
PLUGIN_DOCFLAGS:=$(AV_INCLUDES)
PLUGIN_TESTS_DIRS:=astraver

ifeq ($(FRAMAC_MAKE),yes)
unexport $(FRAMAC_MAKE)
endif

$(PLUGIN_DIR)/interp.cmo: $(PLUGIN_DIR)/interp.cmi $(AVCMA)

$(PLUGIN_DIR)/interp.cmx: $(PLUGIN_DIR)/interp.cmi $(AVCMXA)

RESOURCES   ?= astraver_spec_prolog.h

install::
	$(MKDIR) $(FRAMAC_DATADIR)/astraver
	$(CP) $(addprefix $(PLUGIN_DIR)/share/astraver/,$(RESOURCES)) $(FRAMAC_DATADIR)/astraver

uninstall::
	$(RM) -r $(FRAMAC_DATADIR)/astraver

include $(FRAMAC_SHARE)/Makefile.dynamic
