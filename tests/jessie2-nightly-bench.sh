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
OUT=$REPORTDIR/jessie2.out
PREVIOUS=$REPORTDIR/jessie2.previous
DIFF=$REPORTDIR/jessie2.diff
REPORT=$REPORTDIR/jessie2.report
DATE=`date --utc +%Y-%m-%d`

SUBJECT="Jessie2 nightly bench:"

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


echo "== Jessie2 bench on $DATE ==" > $REPORT
echo "Starting time (UTC): "`date --utc +%H:%M` >> $REPORT

# configuration
autoconf
./configure --enable-local &> $OUT
if test "$?" != "0" ; then
    echo "Configure failed" >> $REPORT
    cat $OUT >> $REPORT
    SUBJECT="$SUBJECT configure failed"
    notify
else
    echo "Configuration succeeded. " >> $REPORT
    grep "Frama-C version" $OUT >> $REPORT
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
# bin/why-config.opt &> $OUT
# if test "$?" != "0" ; then
#     echo "Prover detection in Why2 failed" >> $REPORT
#     cat $OUT >> $REPORT
#     SUBJECT="$SUBJECT prover detection failed"
#     notify
# else
#     echo "Prover detection in Why2 succeeded. " >> $REPORT
# fi

# detection of Why3 and its provers 
why3 --version &> $OUT
if test "$?" != "0" ; then
    echo "why3 --version failed" >> $REPORT
    cat $OUT >> $REPORT
    SUBJECT="$SUBJECT Why3 not found"
    notify
else
    cat $OUT >> $REPORT
fi

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
tests/jessie2-replay.sh &> $OUT
if test "$?" != "0" ; then
    SUBJECT="$SUBJECT failed"
    echo "Proof replay failed" >> $REPORT
else
    SUBJECT="$SUBJECT successful"
    echo " !!! REPLAY SUCCEEDED !!!  YAHOOOO !!! " >> $REPORT
fi

# store the state for this day
cp $OUT $REPORTDIR/jessie2-bench-$DATE

echo "Ending time (UTC): "`date --utc +%H:%M` >> $REPORT

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

