
all: manual.ps doc.ps

doc.dvi: doc.tex rules.tex macros.tex code.tex dep.ps

SRCFILES=../src/loc.mli ../src/logic.mli ../src/types.mli \
	 ../src/ptree.mli ../src/ltyping.mli ../src/ast.mli ../src/env.mli \
         ../src/typing.mli ../src/typing.ml ../src/wp.mli ../src/wp.ml \
	 ../src/monad.mli ../src/monad.ml ../src/mlize.mli ../src/mlize.ml

dep.ps:
	(cd ../src; ocamldep *.ml* | ocamldot | dot -Tps) > dep.ps

code.tex: $(SRCFILES)
	ocamlweb --no-preamble -o $@ $(SRCFILES)

manual.dvi: manual.tex
	latex manual
	latex manual
	makeindex manual
	latex manual

manual.html: manual.tex
	hevea manual.tex

%.dvi: %.tex
	latex $< && latex $<

%.ps: %.dvi
	dvips -o $@ $<

clean::
	rm -f *~ *.dvi *.log *.aux *.toc dep.ps doc.ps manual.ps
