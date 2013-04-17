#!/bin/sh

echo 'Format.eprintf "%s@." (Sys.getcwd());;' | ocaml 1>/dev/null 2> /tmp/regtests.cwd

DIR=`cat /tmp/regtests.cwd`
rm -f /tmp/regtests.cwd
LIBDIR=`grep "libdir" $DIR/src/version.ml | sed -e 's|[^"]*"\([^"]*\)"[^"]*|\1|g' | head -n 1`
LANG=

echofilename () {
  echo "========== file $1 =========="
}

mycat() {
  echofilename $1
  sed -e "s|jessie_[0-9]\+|jessie_<num>|g" $1
}

mycatfilterdir () {
  echofilename $1
  sed -e "s|$DIR|HOME|g" -e "s|$LIBDIR|WHYLIB|g" $1
}

case $1 in
  *.java)
        d=`dirname $1`
	b=`basename $1 .java`
        f=$d/$b
	mycat $f.java
	echo "========== krakatoa execution =========="
	rm -f $f.jc
	rm -f $f.jloc
	opt=""
	if grep JAVACARD $f.java ; then
	    opt=-javacard
	fi
	KRAKATOALIB=$DIR/lib bin/krakatoa.opt -gen-only $opt $1 || exit 1
	mycat $f.jc
	mycatfilterdir $f.jloc
	echo "========== jessie execution =========="
	rm -f $f.makefile
	rm -f $d/why/$b.why
	rm -f $f.loc
	WHYLIB=$DIR/lib bin/jessie.opt -locs $f.jloc -why-opt -split-user-conj $f.jc || exit 2
	mycatfilterdir $f.makefile
	mycatfilterdir $f.loc
	mycat $d/why/$b.why
	echo "========== make project execution =========="
	rm -f $d/why/$b.wpr
	rm -f $d/why/$b'_ctx'.why
	rm -f $d/why/$b'_po'*.why
	WHYLIB=$DIR/lib WHYEXEC=$DIR/bin/why.opt make --quiet -C $d -f $b.makefile project
	mycatfilterdir $d/why/$b.wpr
	mycat $d/why/$b'_ctx'.why
	for i in `ls $d/why/$b'_po'*.why`; do mycat $i; done
	echo "========== generation of Simplify VC output =========="
	WHYLIB=$DIR/lib WHYEXEC=$DIR/bin/why.opt make --quiet -C $d -f $b.makefile simplify/$b'_why'.sx
	mycatfilterdir $d/simplify/$b'_why'.sx
	echo "========== running Simplify =========="
	tmp=$(tempfile -s regtests_simplify)
	DP="$DIR/bin/why-dp.opt -no-timings -timeout 1" WHYLIB=$DIR/lib WHYEXEC=$DIR/bin/why.opt make --quiet -C $d -f $b.makefile simplify 2> $tmp
	grep -v 'CPU time limit' $tmp >&2
	echo "========== generation of alt-ergo VC output =========="
	WHYLIB=$DIR/lib WHYEXEC=$DIR/bin/why.opt make --quiet -C $d -f $b.makefile why/$b'_why'.why
	mycat $d/why/$b'_why'.why
	if grep RUNALTERGO $1 ; then
  	    echo "========== running alt-ergo =========="
	    tmp=$(tempfile -s regtests_ergo)
	    DP="$DIR/bin/why-dp.opt -no-timings -timeout 10" WHYLIB=$DIR/lib WHYEXEC=$DIR/bin/why.opt make --quiet -C $d -f $b.makefile ergo 2> $tmp
	    grep -v 'CPU time limit' $tmp >&2
        fi
	if grep RUNSIMPLIFY $1 ; then
	    echo "========== generation of Simplify VC output =========="
	    WHYLIB=$DIR/lib WHYEXEC=$DIR/bin/why.opt make --quiet -C $d -f $b.makefile simplify/$b'_why'.sx
	    mycatfilterdir $d/simplify/$b'_why'.sx
	    echo "========== running Simplify =========="
	    tmp=$(tempfile -s regtests_simplify)
	    DP="$DIR/bin/why-dp.opt -no-timings -timeout 1" WHYLIB=$DIR/lib WHYEXEC=$DIR/bin/why.opt make --quiet -C $d -f $b.makefile simplify 2> $tmp
	    grep -v 'CPU time limit' $tmp >&2
        fi
	if grep RUNCOQ $f.java ; then
	    echo "========== generation of Coq VC output =========="
	    WHYLIB=$DIR/lib WHYEXEC=$DIR/bin/why.opt make --quiet -C $d -f $b.makefile coq
	    mycatfilterdir $d/coq/$b'_why'.v
	    echo "========== running Coq =========="
	    DP="$DIR/bin/why-dp.opt -no-timings -timeout 100" WHYLIB=$DIR/lib WHYEXEC=$DIR/bin/why.opt make --quiet -C $d -f $b.makefile coq
        fi
	;;
  *.c)
        d=`dirname $1`
	b=`basename $1 .c`
        j=$d/$b.jessie
        f=$j/$b
	mycat $1
	echo "========== frama-c -jessie execution =========="
	rm -f $f.jc
	rm -f $f.cloc
	FRAMAC_PLUGIN=$DIR/frama-c-plugin frama-c -jessie -jessie-gen-only $1 || exit 1
	mycat $f.jc
	mycatfilterdir $f.cloc
	echo "========== jessie execution =========="
	rm -f $f.makefile
	rm -f $j/why/$b.why
	rm -f $f.loc
	WHYLIB=$DIR/lib bin/jessie.opt -locs $f.cloc -why-opt -split-user-conj $f.jc || exit 2
	mycatfilterdir $f.makefile
	mycatfilterdir $f.loc
	mycat $j/why/$b.why
	echo "========== generation of alt-ergo VC output =========="
	WHYLIB=$DIR/lib WHYEXEC=$DIR/bin/why.opt make --quiet -C $j -f $b.makefile why/$b'_why'.why
	mycat $j/why/$b'_why'.why
	if grep RUNALTERGO $1 ; then
	    echo "========== running alt-ergo =========="
	    tmp=$(tempfile -s regtests_ergo)
	    DP="$DIR/bin/why-dp.opt -no-timings -timeout 2" WHYLIB=$DIR/lib WHYEXEC=$DIR/bin/why.opt make --quiet -C $j -f $b.makefile ergo 2> $tmp
	    grep -v 'CPU time limit' $tmp >&2
        fi
	if grep RUNGAPPA $1 ; then
	    echo "========== generation of Gappa VC output =========="
	    WHYLIB=$DIR/lib WHYEXEC=$DIR/bin/why.opt make --quiet -C $j -f $b.makefile gappa/$b'_why'.gappa
	    mycatfilterdir $j/gappa/$b'_why'.gappa
	    echo "========== running Gappa =========="
	    tmp=$(tempfile -s regtests_gappa)
	    DP="$DIR/bin/why-dp.opt -no-timings -timeout 1" WHYLIB=$DIR/lib WHYEXEC=$DIR/bin/why.opt make --quiet -C $j -f $b.makefile gappa 2> $tmp
	    grep -v 'CPU time limit' $tmp >&2
        fi
	if grep RUNSIMPLIFY $1 ; then
	    echo "========== generation of Simplify VC output =========="
	    WHYLIB=$DIR/lib WHYEXEC=$DIR/bin/why.opt make --quiet -C $j -f $b.makefile simplify/$b'_why'.sx
	    mycatfilterdir $j/simplify/$b'_why'.sx
	    echo "========== running Simplify =========="
	    tmp=$(tempfile -s regtests_simplify)
	    DP="$DIR/bin/why-dp.opt -no-timings -timeout 1" WHYLIB=$DIR/lib WHYEXEC=$DIR/bin/why.opt make --quiet -C $j -f $b.makefile simplify 2> $tmp
	    grep -v 'CPU time limit' $tmp >&2
        fi
	if grep RUNCOQ $1 ; then
	    echo "========== generation of Coq VC output =========="
	    WHYLIB=$DIR/lib WHYEXEC=$DIR/bin/why.opt make --quiet -C $j -f $b.makefile coq
	    mycatfilterdir $j/coq/$b'_why'.v
	    echo "========== running Coq =========="
	    DP="$DIR/bin/why-dp.opt -no-timings -timeout 100" WHYLIB=$DIR/lib WHYEXEC=$DIR/bin/why.opt make --quiet -C $j -f $b.makefile coq
        fi
	;;
  *)
	echo "don't know what to do with $1"
	exit 1
esac


