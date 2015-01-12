#/bin/bash

BUILDSRC=$(dirname $(readlink -f $0))/_build/src

make -C $BUILDSRC/../.. -j byte

ocamlc -c -I "$BUILDSRC/why" -I "$BUILDSRC/jc" -o "$BUILDSRC/jc/jc_debug_output.cmo" "$BUILDSRC/../../src/jc/jc_debug_output.ml"

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

load_printer jc_noutput.cmo
load_printer rc.cmo
load_printer version.cmo
load_printer lib.cmo
load_printer jc_position.cmo
load_printer jc_why_output_misc.cmo
load_printer why3_kw.cmo
load_printer jc_why3_output.cmo
load_printer jc_why_output.cmo
load_printer jc_options.cmo
load_printer jc_norm.cmo
load_printer jc_name.cmo
load_printer jc_struct_tools.cmo
load_printer jc_typing.cmo
load_printer jc_effect.cmo
install_printer Jc_effect.print_effect

install_printer Jc_debug_output.expr
install_printer Jc_debug_output.assertion
install_printer Jc_debug_output.term
install_printer Jc_debug_output.string_set
install_printer Jc_debug_output.location
install_printer Jc_debug_output.location_set
set print_depth 3
'
rlwrap -P "$SCRIPT" ocamldebug -I "$BUILDSRC/why" -I "$BUILDSRC/jc" -I "$BUILDSRC/../../src/why" -I "$BUILDSSRC/../../src/jc"\
       $BUILDSRC/../../bin/jessie.byte $@