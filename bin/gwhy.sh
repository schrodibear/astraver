#!/bin/sh

case $1 in
  *.java)
	b=`basename $1 .java`
	krakatoa -gen-only $1 || exit 1
	echo "krakatoa on $b.java done"
        d=`dirname $1`
        echo "cd $d"
        cd $d
	jessie -locs $b.jloc -why-opt -split-user-conj $b.jc || exit 2
	echo "jessie done"
	make -f $b.makefile gui
	;;
  *.c)
	frama-c -jessie -jessie-atp=gui -jessie-why-opt="-split-user-conj" $1 || exit 1
	;;
  *.jc)
	b=`basename $1 .jc`
	jessie -why-opt -split-user-conj $b.jc || exit 1
	make -f $b.makefile gui
	;;
  *.mlw|*.why)
	gwhy-bin -split-user-conj $1
	;;
  *)
	echo "don't know what to do with $1"
esac


