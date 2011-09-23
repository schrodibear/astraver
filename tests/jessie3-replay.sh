#!/bin/bash

JAVA="AllZeros Arrays BinarySearch Counter Creation Fibonacci
      FlagStatic Gcd Hello \
      Isqrt Literals MacCarthy Muller NameConflicts Negate \
      PreAndOld Purse SelectionSort \
      SideEffects SimplAlloc Switch \
      Termination TestNonNull"

JAVATODO="SimpleApplet Sort2 Sort"

C="binary_search clock_drift flag floats_bsearch float_sqrt \
   insertion_sort isqrt minmax muller my_cosine quick_sort \
   rec selection_sort sparse_array2 Sterbenz swap"

CTODO="maze sparse_array heap_sort"

case "$1" in
  "-force")
        REPLAYOPT="-force"
        ;;
  "")
        REPLAYOPT=""
        ;;
  *)
        echo "$0: Unknown option '$1'"
        exit 2
esac


DIR=$PWD
TMP=$DIR/jessie3-regtests.out
TMPERR=$DIR/jessie3-regtests.err
export WHYLIB=$DIR/lib
export KRAKATOALIB=$DIR/lib

res=0

cd tests

printf "\n-------- Java examples --------\n"

cd java

for i in $JAVA; do
    printf "$i.java... "
    ../../bin/krakatoa.opt $i.java 2> $TMPERR > $TMP
    if test "$?" != "0"  ; then
	printf "krakatoa FAILED\n"
    else
        ../../bin/jessie.opt -why3ml -locs $i.jloc $i.jc 2> $TMPERR > $TMP
        if test "$?" != "0"  ; then
	    printf "jessie FAILED\n"
        else
            why3replayer $REPLAYOPT -I $WHYLIB/why3 $i 2> $TMPERR > $TMP
            ret=$?
            if test "$ret" != "0"  ; then
	        printf "replay FAILED (ret code=$ret):"
                out=`head -1 $TMP`
                if test -z "$out" ; then
                    printf "standard error: (standard output empty)"
                    cat $TMPERR
                else
	            cat $TMP
                fi
	        res=1
	    else
	        printf "OK"
	        cat $TMP
	    fi
        fi
    fi
done

cd ..

printf "\n-------- C examples --------\n"

cd c

for i in $C; do
    printf "$i.c... "
    frama-c -load-module ../../frama-c-plugin/Jessie.cmxs -jessie -jessie-gen-only $i.c 2> $TMPERR > $TMP
    if test "$?" != "0"  ; then
	printf "frama-c -jessie FAILED\n"
    else
       ../../bin/jessie.opt -why3ml -locs $i.jessie/$i.cloc $i.jessie/$i.jc 2> $TMPERR > $TMP
        if test "$?" != "0"  ; then
	    printf "jessie FAILED\n"
        else
            why3replayer $REPLAYOPT -I $WHYLIB/why3 $i.jessie/$i 2> $TMPERR > $TMP
            ret=$?
            if test "$ret" != "0"  ; then
	        printf "replay FAILED (ret code=$ret):"
                out=`head -1 $TMP`
                if test -z "$out" ; then
                    printf "standard error: (standard output empty)"
                    cat $TMPERR
                else
	            cat $TMP
                fi
	        res=1
	    else
	        printf "OK"
	        cat $TMP
	    fi
        fi
    fi
done

cd ..

exit $res
