
all: main.ps

main.ps: main.dvi
	dvips $^ -o $@

figabc.eps: figabc.tex
	latex figabc
	dvips -E figabc.dvi -o $@

main.dvi: main.tex figabc.eps
	latex main
	bibtex main
	latex main
	latex main

