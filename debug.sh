#/bin/bash

BUILDSRC=$(dirname $(readlink -f $0))/_build/src

make -C $BUILDSRC/../.. -j byte

ocamlc -c -g -no-alias-deps -open Aliases -I "$BUILDSRC/why" -I "$BUILDSRC/jc" -o "$BUILDSRC/jc/jc_debug_print.d.cmo" "$BUILDSRC/../../src/jc/jc_debug_print.ml"

SCRIPT='load_printer nums.cma
load_printer why_pp.cmo
load_printer jc_stdlib.cmo
load_printer jc_envset.cmo
load_printer jc_common_options.cmo
load_printer jc_region.cmo
load_printer jc_fenv.cmo
load_printer why_loc.cmo
load_printer jc_constructors.cmo
load_printer jc_common.cmo
load_printer jc_print_misc.cmo
load_printer jc_iterators.cmo
load_printer jc_type_var.cmo
load_printer jc_print_p.cmo
load_printer jc_print.cmo
load_printer jc_debug_print.cmo

load_printer jc_print_n.d.cmo
load_printer why_rc.d.cmo
load_printer why_version.d.cmo
load_printer jc_version.d.cmo
load_printer jc_position.d.cmo
load_printer jc_name.d.cmo
load_printer jc_output.d.cmo
load_printer jc_options.d.cmo
load_printer jc_norm.d.cmo
load_printer jc_struct_tools.d.cmo
load_printer jc_typing.d.cmo
load_printer jc_effect.d.cmo
install_printer Jc_effect.print_effect

install_printer Jc_debug_print.expr
install_printer Jc_debug_print.assertion
install_printer Jc_debug_print.term
install_printer Jc_debug_print.string_set
install_printer Jc_debug_print.location
install_printer Jc_debug_print.location_set
set print_depth 3
'
rlwrap -P "$SCRIPT" ocamldebug -I "$BUILDSRC/why" -I "$BUILDSRC/jc" -I "$BUILDSRC/../../src/why" -I "$BUILDSSRC/../../src/jc"\
       $BUILDSRC/../../bin/jessie.byte $@
