AUTOMAKE_OPTIONS = 1.4

AUTOHEADER = echo ""

SUBDIRS=.

# installed binaries

bin_SCRIPTS = octanal octanalopt

# clean

clean-local:
	rm -f *~ *.tmp \#*
	rm -f octanal octanalopt
	rm -f *.cmo *.cmi *.cmx *.cma *.cmxa *.a *.o
	rm -f oct_anal_lex.ml oct_anal_lex.mli oct_anal_yacc.mli oct_anal_yacc.ml oct_anal_yacc.output
	rm -f result.*

distclean-local:
	rm -f Makefile


# OCaml

SUFFIXES = .cmo .cmi .cmx .cma .cmxa

CURDIR := $(shell pwd)

ML = ocamlc
MLN = ocamlopt
MLFLAGS = -I . -I ../ocamllib -ccopt -L../clib/.libs/ -ccopt -L../ocamllib/.libs/ -ccopt -L@libdir@ @MLFLAGS@ 

%.cmi: %.mli
	$(ML) $(MLFLAGS) -c $< -o $@

%.cmo: %.ml
	$(ML) $(MLFLAGS) -c $< -o $@

%.cmx: %.ml
	$(MLN) $(MLFLAGS) -c $< -o $@

octanal: oct_anal_syn.cmo oct_anal_yacc.cmo oct_anal_lex.cmo oct_anal_core.cmo oct_anal.cmo
	$(ML) -custom ../ocamllib/oct.cma @MLMODS@ $(MLFLAGS) $^ -o $@

octanalopt: oct_anal_syn.cmx oct_anal_yacc.cmx oct_anal_lex.cmx oct_anal_core.cmx oct_anal.cmx 
	$(MLN) ../ocamllib/oct.cmxa @MLMODSX@ $(MLFLAGS) $^ -o $@

oct_anal_yacc.ml oct_anal_yacc.mli: oct_anal_yacc.mly
	ocamlyacc -v oct_anal_yacc.mly

oct_anal_lex.ml: oct_anal_lex.mll
	ocamllex oct_anal_lex.mll

oct_anal_yacc.cmo oct_anal_yacc.cmx: oct_anal_yacc.cmi oct_anal_syn.cmo
oct_anal_lex.cmo oct_anal_lex.cmx: oct_anal_syn.cmo
oct_anal.cmo: oct_anal_core.cmo
oct_anal.cmx: oct_anal_core.cmx
oct_anal_core.cmo: ../ocamllib/oct.cma ../ocamllib/oct.cmi
oct_anal_core.cmx: ../ocamllib/oct.cmxa ../ocamllib/oct.cmi

# uninstall

uninstall-local:
	rm -f $(DESTDIR)$(bindir)/octanal
	rm -f $(DESTDIR)$(bindir)/octanalopt

# dist

EXTRA_DIST = oct_anal.ml oct_anal_core.ml oct_anal_lex.mll oct_anal_syn.ml oct_anal_yacc.mly oct_anal_examples
