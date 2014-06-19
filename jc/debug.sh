#/bin/bash

DIR=$(dirname $(readlink -f $0))

ocamlc -c -I "$DIR/../src/" -o "$DIR/jc_debug_output.cmo" "$DIR/jc_debug_output.ml"

make -C $DIR/.. byte

SCRIPT='load_printer nums.cma
load_printer pp.cmo
load_printer jc_stdlib.cmo
load_printer jc_envset.cmo
load_printer option_misc.cmo
load_printer jc_common_options.cmo
load_printer jc_region.cmo
load_printer jc_fenv.cmo
load_printer loc.cmo
load_printer jc_constructors.cmo
load_printer jc_pervasives.cmo
load_printer jc_output_misc.cmo
load_printer jc_iterators.cmo
load_printer jc_type_var.cmo
load_printer jc_poutput.cmo
load_printer jc_output.cmo
load_printer jc_debug_output.cmo
install_printer Jc_debug_output.expr
install_printer Jc_debug_output.assertion
install_printer Jc_debug_output.term
set print_depth 3
'
rlwrap -P "$SCRIPT" ocamldebug -I "$DIR/../src/" -I "$DIR" $DIR/../bin/jessie.byte $@
