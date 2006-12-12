
all: slides-pp.pdf

%-pp.tex: pp.ml %.tex 
	ocaml $^ > $@

pp.ml: pp.mll
	ocamllex pp.mll

%.pdf: %.tex 
	pdflatex $^

slides-pp.ps: slides-pp.tex
	latex $^
	latex $^
	dvips -P pdf -ta4 slides-pp.dvi -o tmp.ps
	psnup -1 -W128mm -H96mm -pa4 tmp.ps $@

print: slides-pp.ps
	psnup -l -8 slides-pp.ps | lpr


wc:
	fgrep "\begin{frame}" slides.tex | wc -l