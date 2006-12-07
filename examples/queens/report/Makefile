
all: main.ps

main.ps: main.dvi
	dvips $^ -o $@

main.dvi: main.tex
	latex main
	bibtex main
	latex main
	latex main

