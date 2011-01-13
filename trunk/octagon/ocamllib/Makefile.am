AUTOMAKE_OPTIONS = 1.4

AUTOHEADER = echo ""

SUBDIRS=.

# installed binaries

WITH_OCAML = @with_ocaml@
OCAML_INST = oct.cma oct.cmxa oct.a oct.cmi oct.mli \
	     oct_LIBSUFFIX.cma oct_LIBSUFFIX.cmxa \
	     oct_LIBSUFFIX.a oct_LIBSUFFIX.cmi oct_LIBSUFFIX.mli

bin_SCRIPTS = octtop-LIBSUFFIX
noinst_SCRIPTS = oct.ml oct.mli oct.cma oct.cmxa oct.a oct.cmi \
	     oct_LIBSUFFIX.cma oct_LIBSUFFIX.cmxa \
	     oct_LIBSUFFIX.a oct_LIBSUFFIX.cmi oct_LIBSUFFIX.mli

# installed headers

configincludedir = $(includedir)/oct
liboctincludedir = $(includedir)/oct
liboctinclude_HEADERS = oct_ocaml.h

# C

lib_LTLIBRARIES = libocamloct.la libocamloct_LIBSUFFIX.la

libocamloct_la_SOURCES = oct_ocaml.c
libocamloct_LIBSUFFIX_la_SOURCES = oct_ocaml.c

AM_CFLAGS=-I. -I../clib @CFLAGS@ @EXTRA_DEFS@


# OCaml

SUFFIXES = .cmo .cmi .cmx .cma .cmxa

CURDIR := $(shell pwd)

ML = ocamlc
MLN = ocamlopt
MLTOP = ocamlmktop
MLFLAGS = -I . @MLFLAGS@
EXTRA_MLFLAGS = -ccopt -L.libs/ -ccopt -L../clib/.libs/ -ccopt -L@libdir@ @EXTRA_MLFLAGS@

%.cmi: %.mli
	$(ML) $(MLFLAGS) -c $< -o $@

%.cmo: %.ml %.cmi
	$(ML) $(MLFLAGS) -c $< -o $@

%.cmx: %.ml %.cmi
	$(MLN) $(MLFLAGS) -c $< -o $@

%.cma: oct.cmo oct_LIBSUFFIX.cmo \
		   ../clib/liboct_LIBSUFFIX.la libocamloct_LIBSUFFIX.la
	$(ML) -cclib -static -a -custom $< $(MLFLAGS) $(EXTRA_MLFLAGS) -o $@

%.cmxa: oct.cmx oct_LIBSUFFIX.cmx \
		   ../clib/liboct_LIBSUFFIX.la libocamloct_LIBSUFFIX.la
	$(MLN) -cclib -static -a $< $(MLFLAGS) $(EXTRA_MLFLAGS) -o $@


octtop-LIBSUFFIX: oct_LIBSUFFIX.cma
	$(MLTOP) -custom oct_LIBSUFFIX.cma $(MLFLAGS) -o $@

oct.ml: @OCAML_ML@ ../oct_config_2.h
	rm -rf $@
	cat @OCAML_ML@ > $@

oct.mli: @OCAML_MLI@ ../oct_config_2.h
	rm -rf $@
	cat @OCAML_MLI@ > $@

oct_LIBSUFFIX.ml: oct.ml
	rm -rf $@
	cp $< $@

oct_LIBSUFFIX.mli: oct.mli
	rm -rf $@
	cp $< $@


install-exec-local: $(OCAML_INST)
	$(mkinstalldirs) $(DESTDIR)$(WITH_OCAML)/oct
	for i in $(OCAML_INST); do\
		$(INSTALL) -m 644 $$i $(DESTDIR)$(WITH_OCAML)/oct/$$i;\
	done

# uninstall

uninstall-local:
	rm -rf $(DESTDIR)$(WITH_OCAML)/oct
	rm -f $(DESTDIR)$(libdir)/libocamloct_*
	rm -f $(DESTDIR)$(bindir)/octtop-*

# clean

clean-local:
	rm -f oct.ml oct.mli oct_LIBSUFFIX.ml oct_LIBSUFFIX.mli
	rm -f octtop-* libocamloct_*.la
	rm -f *.a *.cma *.cmo *.cmx *.cmi *.cmxa
	rm -f *~ *.tmp \#*

# dist

distclean-local:
	rm -f Makefile


EXTRA_DIST = oct_common.ml oct_common.mli oct_polka.mli oct_gmp.mli
