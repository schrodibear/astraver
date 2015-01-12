#!/bin/sh

# Note: the BINDIR variable is a free variable
# Note: the LIBDIR variable is a free variable
# Note: the COQVER variable is a free variable
# Note: the mkdirs are needed for the Ocamlbuild Makefile.

. ./Version

# Why
WHYVF=src/why/why_version.ml
mkdir -p src/why
echo "let coqversion = \"$COQVER\"" > $WHYVF
echo "let version = \"$WHY_VERSION\"" >> $WHYVF
echo "let date = \""`date -R`"\"" >> $WHYVF
echo "let bindir = \"$BINDIR\"" >> $WHYVF
echo "let libdir = \"$LIBDIR/why\"" >> $WHYVF

# Jessie2
JCVF=src/jc/jc_version.ml
mkdir -p src/jc
echo "let version = \"$JC_VERSION\"" >> $JCVF
echo "let date = \""`date -R`"\"" >> $JCVF

# Doc
DOCF=doc/version.tex
mkdir -p doc
printf '\\newcommand{\\whyversion}{'$VERSION'}\n' > $DOCF
printf '\\newcommand{\\caduceusversion}{'$CVERSION'}\n' >> $DOCF
