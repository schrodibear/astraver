#!/bin/sh

mycat() {
  echo "========== file $1 =========="
  cat $1
}

case $1 in
  *.java)
        d=`dirname $1`
	b=`basename $1 .java`
        f=$d/$b
	echo "========== krakatoa execution =========="
	rm -f $f.jc
	rm -f $f.jloc
	bin/krakatoa.opt $1 || exit 1
	mycat $f.jc 
	mycat $f.jloc
	echo "========== jessie execution =========="
	rm -f $f.makefile 
	rm -f $d/why/$b.why
	bin/jessie.opt -locs $f.jloc -why-opt -split-user-conj $f.jc || exit 2
	mycat $f.makefile
	mycat $d/why/$b.why
	echo "========== make project execution =========="
	rm -f $d/why/$b.wpr	
	rm -f $d/why/$b'_ctx'.why	
	rm -f $d/why/$b'_po'*.why
	make -C $d -f $b.makefile project
	mycat $d/why/$b.wpr	
	mycat $d/why/$b'_ctx'.why	
	for i in $d/why/$b'_po'*.why; do mycat $i; done
	echo "========== simplify execution =========="
	DPOPT=-no-timings TIMEOUT=1 make -C $d -f $b.makefile simplify	
	echo "========== ergo execution =========="
	DPOPT=-no-timings TIMEOUT=1 make -C $d -f $b.makefile ergo	
	;;
  *.c)
	b=`basename $1 .c`
	exit 1
	caduceus -why-opt -split-user-conj $1 || exit 1
	make -f $b.makefile gui
	;;
  *.jc)
	b=`basename $1 .jc`
	exit 1
	jessie $b.jc || exit 1
	make -f $b.makefile gui
	;;
  *.why)
	exit 1
	gwhy-bin -split-user-conj $1
	;;
  *)
	echo "don't know what to do with $1"
	exit 1
esac


