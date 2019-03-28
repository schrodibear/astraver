#!/bin/bash

# Note: the BINDIR variable is a free variable
# Note: the LIBDIR variable is a free variable
# Note: the COQVER variable is a free variable
# Note: the mkdirs are needed for the Ocamlbuild Makefile.

. ./Version

# AstraVer
GIT=$(git rev-parse HEAD 2>/dev/null)
if [[ -n "$GIT" ]]; then
  GIT="git commit ${GIT:0:8}"
  if output=$(git status --porcelain) && [[ -n "$output" ]]; then
    GIT="dirty ${GIT}"
  fi
  GIT=" (${GIT})"
fi
AV_VERSION="${AV_VERSION}${GIT}"
AVVF=src/av/version.ml
mkdir -p src/av
echo "let version = \"$AV_VERSION\"" > $AVVF
echo "let date = \""`date -R`"\"" >> $AVVF
echo "let libdir = \"$LIBDIR/astraver\"" >> $AVVF

# Doc
DOCF=doc/version.tex
mkdir -p doc
printf '\\newcommand{\\whyversion}{'$VERSION'}\n' > $DOCF
printf '\\newcommand{\\caduceusversion}{'$CVERSION'}\n' >> $DOCF
