
all: why-manual.dvi doc.dvi

doc.dvi: doc.tex rules.tex macros.tex code.tex dep.ps

SRCFILES=ident.mli 

dep.ps::
	(cd ../src; ocamldep *.ml* | ocamldot | dot -Tps) > dep.ps

code.tex::
	cd ../src; ocamlweb --no-preamble -o ../doc/code.tex $(SRCFILES)

%.dvi: %.tex
	latex $< && latex $<

%.ps: %.dvi
	dvips -o $@ $<

clean::
	rm -f *~ *.dvi *.log *.aux *.toc
