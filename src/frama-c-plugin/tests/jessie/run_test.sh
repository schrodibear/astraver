suffix=$2
dir=`dirname $0`
name=`echo $1 | cut -d"." -f1`
if [ "$name.c" != "$1" ]
then
	echo "run_test: name of test \"$1\" should match \"$name.c\""
	exit 1
fi
cd "$dir"
file=`basename "$name"`
export PPCHOME=`(cd ../..; pwd -P)`
export WHYHOME=`(cd  ../../..; pwd -P)`
options=`grep "@PPC_OPTIONS:" $file.c`
options=`echo $options | cut -c14-`
export PPC_OPTIONS="-journal-disable $options"
options=`grep "@JC_OPTIONS:" $file.c`
options=`echo $options | cut -c13-`
export JC_OPTIONS="$options"
export MAKEFLAGS=
make --quiet "$file.$suffix"
