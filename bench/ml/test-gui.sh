#!/bin/sh

TMPDIR=tmp

mkdir -p $TMPDIR/why
cp good/$*.ml $TMPDIR
cd $TMPDIR

../../../bin/jessica.opt ../pervasives.mli $1.ml
../../../bin/jessie.opt -why-opt --split-user-conj $1.jc
make -f $*.makefile gui