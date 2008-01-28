#!/bin/sh

JCKLOG=$1-jessica.log
JCLOG=$1-jessie.log
WHYLOG=$1-why.log

if ../../../bin/jessie.opt $1.jc 2>> $JCLOG >> $JCLOG
then
    cat jessie.log >> $JCLOG
    if make -f $1.makefile goals 2>> $WHYLOG >> $WHYLOG
    then
	echo "$1.jc: OK"
	mv $1.jc $1.jc.bak
    else
	echo "$1.jc: Why FAILED"
    fi
else
    cat jessie.log >> $JCLOG
    echo "$1.jc: Jessie FAILED"
fi