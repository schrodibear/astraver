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
        if [[ "$i" =~ enum.Bit_u?int(8|16|32)$ ]]; then
            echo "  remove prop To_int_def" >>$DRIVER
        fi
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
    echo "import \"${WHY3DATADIR}/drivers/coq.drv\"" >> ./coq.gen
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

function generate_makefile
{
    MAKEFILE=./Makefile
    echo  >$MAKEFILE
    jobs=""
    for i in $THS; do jobs=$jobs" ${i##*\.}.vo"; done
    echo "all: $jobs" >>$MAKEFILE
    echo >>$MAKEFILE
    echo "WHY3LIBDIR=\$(shell why3 --print-libdir)" >>$MAKEFILE
    echo >>$MAKEFILE
    for i in $THS; do
        file="${i##*\.}"
        th_deps=$(grep -oE 'Require [A-Z][A-Za-z_0-9]+' ${file}.v | cut -d ' ' -f 2 | grep -vE 'Import|BuiltIn|Int$' | tr '\n' ' ')
        deps=""
        for j in $th_deps; do deps=$deps" ${j}.vo"; done
        echo "${file}.vo: ${file}.v $deps" >>$MAKEFILE
        echo -e "\tcoqc -R \$(WHY3LIBDIR)/coq Why3 -R . Astraver $<" >>$MAKEFILE
        echo >>$MAKEFILE
    done
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
echo "Generating Makefile"
generate_makefile
echo "Cleaning up"
rm -f ./coq.gen
echo "Finished"
