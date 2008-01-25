#!/bin/sh

TMPDIR=tmp

mkdir -p $TMPDIR/why
cp good/$*.ml $TMPDIR
cd $TMPDIR

if ../../../bin/jessica.opt ../pervasives.mli $1.ml
then
    if ../../../bin/jessie.opt -why-opt --split-user-conj $1.jc
    then
	make -f $1.makefile coq
    fi
fi