
all: manual.ps doc.ps

doc.dvi: doc.tex rules.tex macros.tex code.tex dep.ps

SRCFILES=ast.mli typing.mli typing.ml monad.mli monad.ml mlize.mli mlize.ml

dep.ps::
	(cd ../src; ocamldep *.ml* | ocamldot | dot -Tps) > dep.ps

code.tex::
	cd ../src; ocamlweb --no-preamble -o ../doc/code.tex $(SRCFILES)

manual.dvi: manual.tex
	latex manual
	latex manual
	makeindex manual
	latex manual

%.dvi: %.tex
	latex $< && latex $<

%.ps: %.dvi
	dvips -o $@ $<

clean::
	rm -f *~ *.dvi *.log *.aux *.toc dep.ps doc.ps manual.ps
