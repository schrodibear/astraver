#!/bin/bash

JAVA="AllZeros ArrayMax Arrays BinarySearch Counter Creation
      Fibonacci FlagStatic Fresh Gcd Hello \
      Isqrt Literals MacCarthy Muller NameConflicts Negate \
      PreAndOld Purse SelectionSort \
      SideEffects SimpleAlloc Switch \
      Termination TestNonNull TreeMax"

JAVATODO="Duplets SimpleApplet Sort2 Sort"

C="array_max binary_search clock_drift duplets \
   find_array flag floats_bsearch float_sqrt \
   insertion_sort isqrt minmax muller my_cosine quick_sort \
   rec scalar_product selection_sort sparse_array2 \
   Sterbenz swap tree_max"

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

report_error () {
    printf "$2 FAILED (ret code=$1)\n"
    printf "standard error:\n"
    cat $TMPERR
    printf "standard output:\n"
    cat $TMP
    res=1
}

cd tests

printf "\n-------- Java examples --------\n"

cd java

for i in $JAVA; do
    printf "$i.java... "
    ../../bin/krakatoa.opt -gen-only $i.java 2> $TMPERR > $TMP
    ret=$?
    if test "$ret" != "0"  ; then
	report_error $ret "krakatoa"
    else
        ../../bin/jessie.opt -why3ml -locs $i.jloc $i.jc 2> $TMPERR > $TMP
        ret=$?
        if test "$ret" != "0"  ; then
	    report_error $ret "jessie"
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
    ret=$?
    if test "$ret" != "0"; then
	report_error $ret "frama-c -jessie"
    else
       ../../bin/jessie.opt -why3ml -locs $i.jessie/$i.cloc $i.jessie/$i.jc 2> $TMPERR > $TMP
       ret=$?
       if test "$ret" != "0"; then
	   report_error $ret "jessie"
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
