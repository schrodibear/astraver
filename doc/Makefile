HEVEA=hevea -charset ISO-8859-1

all: main.pdf manual.ps doc.ps caduceus.ps $(KFILES) krakatoa.pdf

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
	Flag_swap.pp Flag_body.pp \
	contracts.bnf lexpr.bnf

dep.ps:
	(cd ../src; ocamldep *.ml* | ocamldot | dot -Tps) > dep.ps

code.tex: $(SRCFILES)
	ocamlweb --no-preamble -o $@ $(SRCFILES)

logo-why.pdf: logos.tex
	pdflatex logos.tex

logo-why.png: logo-why.pdf
	pdftoppm logos.pdf | pnmcrop | pnmtopng > logowhy.png

logo-why-small.png:

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

krakatoa.html: krakatoa.tex
	rm -f krakatoa.aux
	$(HEVEA) krakatoa.tex
	$(HEVEA) krakatoa.tex

main.html: main.tex
	rm -f main.aux
	$(HEVEA) main.tex
	$(HEVEA) main.tex


main.pdf: 
	pdflatex main.tex


%.pp: %.tex pp
	./pp -color $< > $@

%.pp: %.c pp
	./pp -color -c $< > $@

%.pp: %.java pp
	./pp -color -java $< > $@

%.dvi: %.tex
	latex $< && latex $<

%.ps: %.dvi
	dvips -o $@ $<

%.eps: %.dia
	dia --filter=eps-builtin $^

%.pdf: %.eps
	epstopdf $^

%.tex: %.dia
	dia --filter=tex $^

%.png: %.dia
	dia --filter=png --size=2048,1536 $^

%.bnf: %.tex tex2bnf
	./tex2bnf < $< > $@

tex2bnf: tex2bnf.ml
	ocamlopt.opt -o $@ $^

pp: pp.ml
	ocamlopt.opt -o $@ $^

%.ml: %.mll
	ocamllex.opt $<

clean::
	rm -f *~ *.dvi *.log *.aux *.toc \
	dep.ps doc.ps manual.ps caduceus.ps krakatoa.pdf main.pdf 

