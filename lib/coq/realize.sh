#!/bin/bash

echo "Removing old realizations"
rm -rf ./*.v

function grep_ths
{
   grep -o 'theory .*' ../why3/$1.mlw | cut -d ' ' -f 2 | sed "s/.*/$1.&/"
}

function generate_driver
{
    DRIVER=../why3/coq.drv
    echo >$DRIVER
    for i in $THS; do
        echo "theory $i" >>$DRIVER
        echo "  meta \"realized_theory\" \"$i\", \"${i##*\.}\"" >>$DRIVER
        echo "end" >>$DRIVER
        echo >>$DRIVER
    done
}

function patch_driver
{
    WHY3DATADIR=$(why3 --print-datadir)
    WHY3DATADIR=${WHY3DATADIR//\//\\\/}
    cp $DRIVER ./coq.gen
    sed -e "s/WHY3DATADIR/$WHY3DATADIR/g" ./coq.drv >> ./coq.gen
}

function realize_theories
{
    for i in $THS; do
        echo "  Realizing $i"
        why3 realize -L ../why3 -D coq.gen -o . -T $i&
    done
    wait

    for i in lib_*; do
        j=${i##lib_}
        j=${j//_null/}
        echo "  Moving $i to $j"
        mv $i $j
    done
}

function generate_compilation_script
{
    COMPILING=./compile.sh
    echo "#!/bin/bash" >$COMPILING
    echo >>$COMPILING
    echo "if [ ! -f \${1}o ]; then" >>$COMPILING
    echo "  WHY3LIBDIR=\$(why3 --print-libdir)" >>$COMPILING
    echo "  declare -A PID" >>$COMPILING
    echo >>$COMPILING
    for i in $THS; do
        file="${i##*\.}"
        deps=$(grep -oE 'Require [A-Z][A-Za-z_0-9]+' ${file}.v | cut -d ' ' -f 2 | grep -vE 'Import|BuiltIn|Int' | tr '\n' ' ')
        echo "  for p in $deps; do wait \${PID[\"\$p\"]}; done " >>$COMPILING
        echo "  coqc -R \${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/${file}.v&" >>$COMPILING
        echo "  PID[\"$file\"]=\$!" >>$COMPILING
    done
    echo "  wait" >>$COMPILING
    echo "fi" >>$COMPILING
    chmod +x $COMPILING
}

CORE=$(grep_ths core)
ENUM=$(grep_ths enum)
THS="$CORE $ENUM"

echo "Generating driver"
generate_driver
echo "Patching custom Coq driver"
patch_driver
echo "Realizing theories"
realize_theories
echo "Generating compilation script"
generate_compilation_script
echo "Cleaning up"
rm -f ./coq.gen
echo "Finished"
