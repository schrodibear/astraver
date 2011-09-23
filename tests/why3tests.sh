#!/bin/sh
# regression tests for why3

TMP=/tmp/why3tests.out
TMPERR=/tmp/why3tests.err

cd `dirname $0`

res=0

run () {
    d=`dirname $1`
    echo -n "Replaying $d ... "
    why3replayer -I ../lib/why3 $d 2> $TMPERR > $TMP
    ret=$?
    if test "$ret" != "0"  ; then
	echo -n "FAILED (ret code=$ret):"
        out=`head -1 $TMP`
        if test -z "$out" ; then
            echo "standard error: (standard output empty)"
            cat $TMPERR
        else
	    cat $TMP
        fi
	res=1
    else
	echo -n "OK"
	cat $TMP
    fi
}

echo "=== C examples ==="
# for i in c/my_cosine.c c/selection_sort.c; do # `ls c/*.c`; do
#     frama-c -jessie -jessie-atp=why3ml $i
# done
for i in `ls c/*.jessie/*/why3session.xml`; do
    run $i
done
echo ""


echo "=== Java examples ==="
for i in java/MacCarthy.java; do # `ls java/*.java`; do
    d=`dirname $i`
    f=`basename $i .java`
    (cd $d; krakatoa $f.java)
    jessie -why3ml -locs $d/$f.jloc $d/$f.jc
done
for i in `ls java/*/why3session.xml`; do
    run $i
done
echo ""
