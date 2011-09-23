#!/bin/bash

case "$1" in
  "-mail")
        REPORTBYMAIL=yes
        ;;
  "")
        REPORTBYMAIL=no
        ;;
  *)
        echo "$0: Unknown option '$1'"
        exit 2
esac

REPORTDIR=$PWD/..
OUT=$REPORTDIR/jessie3.out
PREVIOUS=$REPORTDIR/jessie3.previous
DIFF=$REPORTDIR/jessie3.diff
REPORT=$REPORTDIR/jessie3.report
DATE=`date --utc +%Y-%m-%d`

SUBJECT="Jessie3 nightly bench:"

notify() {
    if test "$REPORTBYMAIL" = "yes"; then
        mail -s "$SUBJECT" why3-commits@lists.gforge.inria.fr < $REPORT
        # mail -s "$SUBJECT" Claude.Marche@inria.fr < $REPORT
    else
        # echo "See the file $REPORT"
        cat $REPORT
    fi
    exit 0
}


echo "== Jessie3 bench on $DATE ==" > $REPORT

# configuration
autoconf
./configure &> $OUT
if test "$?" != "0" ; then
    echo "Configure failed" >> $REPORT
    cat $OUT >> $REPORT
    SUBJECT="$SUBJECT configure failed"
    notify
else
    echo "Configuration succeeded. " >> $REPORT
fi

# compilation
make &> $OUT
if test "$?" != "0" ; then
    echo "Compilation failed" >> $REPORT
    tail -20 $OUT >> $REPORT
    SUBJECT="$SUBJECT compilation failed"
    notify
else
    echo "Compilation succeeded. " >> $REPORT
fi

# detection of provers
bin/why-config.opt &> $OUT
if test "$?" != "0" ; then
    echo "Prover detection in Why2 failed" >> $REPORT
    cat $OUT >> $REPORT
    SUBJECT="$SUBJECT prover detection failed"
    notify
else
    echo "Prover detection in Why2 succeeded. " >> $REPORT
fi

# detection of provers in Why3
why3config --detect &> $OUT
if test "$?" != "0" ; then
    echo "Prover detection in Why3 failed" >> $REPORT
    cat $OUT >> $REPORT
    SUBJECT="$SUBJECT prover detection failed"
    notify
else
    echo "Prover detection in Why3 succeeded. " >> $REPORT
fi

# replay proofs
tests/jessie3-replay.sh &> $OUT
if test "$?" != "0" ; then
    SUBJECT="$SUBJECT failed"
    echo "Proof replay failed" >> $REPORT
else
    SUBJECT="$SUBJECT successful"
    echo " !!! REPLAY SUCCEEDED !!!  YAHOOOO !!! " >> $REPORT
fi

# store the state for this day
cp $OUT $REPORTDIR/jessie3-bench-$DATE

# output the diff against previous run
diff -u $PREVIOUS $OUT &> $DIFF
if test "$?" == 0 ; then
    echo "---------- No difference with last bench ---------- " >> $REPORT
else
    echo "" >> $REPORT
    echo "--------------- Diff with last bench --------------" >> $REPORT
    echo "" >> $REPORT
    sed '1,2d' $DIFF >> $REPORT
    cp $OUT $PREVIOUS
fi

# finally print the full state
echo "" >> $REPORT
echo "-------------- Full current state --------------" >> $REPORT
echo "" >> $REPORT
cat $OUT >> $REPORT

# final notification after the replay
notify

