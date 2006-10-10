AUTOMAKE_OPTIONS = 1.4

lib_suffix = @lib_suffix@

AUTOHEADER = echo ""

SUBDIRS=.

# documentation

DOC = doc_oct.pdf
pkgdata_DATA = $(DOC)

doc_oct.pdf: doc_oct.tex
	latex doc_oct
	makeindex doc_oct
	bibtex doc_oct
	latex doc_oct
	latex doc_oct
	dvips doc_oct.dvi -o
	ps2pdf doc_oct.ps


# clean

clean-local:
	rm -f *~ *.tmp \#*
	rm -f *.aux *.bbl *.toc *.blg *.idx *.ilg *.ind *.log *.dvi


# dist

distclean-local:
	rm -f Makefile

EXTRA_DIST = bib_oct.bib doc_oct.tex 
