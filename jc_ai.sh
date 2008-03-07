#!/bin/sh

# Note: the mkdir is needed for the Ocamlbuild Makefile.
mkdir -p jc

if test $APRON = "yes" ; then
    echo "# 1 \"jc/jc_annot_inference.ml\"" > jc/jc_ai.ml;
    cat jc/jc_annot_inference.ml >> jc/jc_ai.ml;
else
    echo "# 1 \"jc/jc_annot_fail.ml\"" > jc/jc_ai.ml;
    cat jc/jc_annot_fail.ml >> jc/jc_ai.ml;
fi