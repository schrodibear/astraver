
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

manual.ps: manual.tex
	latex manual
	latex manual
	makeindex manual
	latex manual
	dvips manual.dvi -o manual.ps

manual.html: manual.tex
	hevea manual.tex

caduceus.ps: caduceus.tex
	latex caduceus
	latex caduceus
	makeindex caduceus
	latex caduceus
	dvips caduceus.dvi -o caduceus.ps

caduceus.html: caduceus.tex
	hevea caduceus.tex

%.dvi: %.tex
	latex $< && latex $<

%.ps: %.dvi
	dvips -o $@ $<

clean::
	rm -f *~ *.dvi *.log *.aux *.toc dep.ps doc.ps manual.ps caduceus.ps

