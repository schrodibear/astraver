#!/bin/sh

JCKLOG=$1-jessica.log
JCLOG=$1-jessie.log
WHYLOG=$1-why.log

echo "jessica $1.ml"
if ../../../bin/jessica.opt ../pervasives.mli $1.ml 2>> $JCKLOG >> $JCKLOG
then
    echo "jessie  $1.jc"
    if ../../../bin/jessie.opt $1.jc 2>> $JCLOG >> $JCLOG
    then
	echo "why     $1.why"
	if ! make -f $1.makefile goals 2>> $WHYLOG >> $WHYLOG
	then
	    echo "  /!\\ ERROR in $1.why"
	fi
    else
	echo "  /!\\ ERROR in $1.jc"
    fi
else
    echo "  /!\\ ERROR in $1.ml"
fi
echo "jessie  $1.jc"
echo "why     $1.why"