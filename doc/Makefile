HEVEA=hevea -charset ISO-8859-1

all: manual.ps doc.ps caduceus.ps $(KFILES) krakatoa.pdf

doc.dvi: doc.tex rules.tex macros.tex code.tex dep.ps

SRCFILES=../src/loc.mli ../src/logic.mli ../src/types.mli \
	 ../src/ptree.mli ../src/ltyping.mli ../src/ast.mli ../src/env.mli \
         ../src/typing.mli ../src/typing.ml ../src/wp.mli ../src/wp.ml \
	 ../src/monad.mli ../src/monad.ml ../src/mlize.mli ../src/mlize.ml

KFILES=Lesson1_max.pp \
	Lesson1_sqrt.pp Lesson1_sqrtbody.pp Lesson1_sqrtloopinv.pp \
	Arrays_findMax.pp Arrays_findMax2.pp Arrays_shift.pp \
	Purse.pp Purse_test1.pp Purse_test2.pp Purse2.pp \
	Purse_withdraw2.pp \
	Flag1.pp Flag_inv.pp Flag_isMonochrome.pp Flag_flag.pp \
	Flag_swap.pp Flag_body.pp

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
	rm -f manual.aux
	$(HEVEA) manual.tex
	$(HEVEA) manual.tex

caduceus.ps: caduceus.tex
	latex caduceus
	latex caduceus
	makeindex caduceus
	latex caduceus
	dvips caduceus.dvi -o caduceus.ps

caduceus.html: caduceus.tex
	rm -f caduceus.aux
	$(HEVEA) caduceus.tex
	$(HEVEA) caduceus.tex

krakatoa.pdf: $(KFILES)
	pdflatex krakatoa.tex


%.pp: %.tex pp.ml
	ocaml pp.ml -color $< > $@

%.pp: %.c pp.ml
	ocaml pp.ml -color -c $< > $@

%.pp: %.java pp.ml
	ocaml pp.ml -color -java $< > $@

pp.ml: pp.mll
	ocamllex pp.mll

%.dvi: %.tex
	latex $< && latex $<

%.ps: %.dvi
	dvips -o $@ $<

clean::
	rm -f *~ *.dvi *.log *.aux *.toc dep.ps doc.ps manual.ps caduceus.ps

