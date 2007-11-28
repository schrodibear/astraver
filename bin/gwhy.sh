#!/bin/sh

case $1 in
  *.java)
	b=`basename $1 .java`
	krakatoa -ignore-overflow $1 || exit 1
	jessie -locs $b.jloc -inv-sem arguments -why-opt -split-user-conj $b.jc || exit 2
	make -f $b.makefile gui
	;;
  *.c)
	b=`basename $1 .c`
	caduceus -why-opt -split-user-conj $1 || exit 1
	make -f $b.makefile gui
	;;
  *.jc)
	b=`basename $1 .jc`
	jessie $b.jc || exit 1
	make -f $b.makefile gui
	;;
  *.why)
	gwhy-bin $1
	;;
  *)
	echo "don't know what to do with $1"
esac


