#!/bin/sh

TMPDIR=tmp

mkdir -p $TMPDIR/why
cp good/$*.ml $TMPDIR
cd $TMPDIR

if ocamlrun -bt ../../../bin/jessica.byte ../pervasives.mli $1.ml
then
    if ocamlrun -bt ../../../bin/jessie.byte -why-opt --split-user-conj $1.jc
    then
	make -f $1.makefile gui
    fi
fi