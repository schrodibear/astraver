#!/bin/sh

JCKLOG=$1-jessica.log
JCLOG=$1-jessie.log
WHYLOG=$1-why.log

if ../../../bin/jessica.opt ../pervasives.mli $1.ml 2>> $JCKLOG >> $JCKLOG
then
    if ../../../bin/jessie.opt $1.jc 2>> $JCLOG >> $JCLOG
    then
	if make -f $1.makefile goals 2>> $WHYLOG >> $WHYLOG
	then
	    echo "$1.ml: OK"
	    mv $1.ml $1.ml.bak
	else
	    echo "$1.ml: Why FAILED"
	fi
    else
	echo "$1.ml: Jessie FAILED"
    fi
else
    echo "$1.ml: Jessica FAILED"
fi