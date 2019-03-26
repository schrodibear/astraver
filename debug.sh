#/bin/bash

BUILDSRC=$(dirname $(readlink -f $0))/_build/src

make -C $BUILDSRC/../.. -j byte

ocamlc -c -g -no-alias-deps -open Aliases -I "$BUILDSRC/why" -I "$BUILDSRC/av" -o "$BUILDSRC/av/av_debug_print.cmo" "$BUILDSRC/../../src/av/av_debug_print.ml"

SCRIPT='load_printer str.cma
load_printer nums.cma
load_printer why_pp.cmo
load_printer av_stdlib.cmo
load_printer av_envset.cmo
load_printer av_common_options.cmo
load_printer av_region.cmo
load_printer av_fenv.cmo
load_printer why_loc.cmo
load_printer av_constructors.cmo
load_printer av_common.cmo
load_printer av_print_misc.cmo
load_printer av_iterators.cmo
load_printer av_type_var.cmo
load_printer av_print_p.cmo
load_printer av_print.cmo
load_printer av_debug_print.cmo

load_printer av_print_n.d.cmo
load_printer why_rc.d.cmo
load_printer why_version.d.cmo
load_printer av_version.d.cmo
load_printer av_position.d.cmo
load_printer av_name.d.cmo
load_printer av_output.d.cmo
load_printer av_common_options.d.cmo
load_printer av_options.d.cmo
load_printer av_norm.d.cmo
load_printer av_struct_tools.d.cmo
load_printer av_typing.d.cmo
load_printer av_effect.d.cmo

install_printer Av_effect.print_effect
install_printer Av_debug_print.expr
install_printer Av_debug_print.assertion
install_printer Av_debug_print.term
install_printer Av_debug_print.string_set
install_printer Av_debug_print.location
install_printer Av_debug_print.location_set
set print_depth 3
'
rlwrap -P "$SCRIPT" ocamldebug -I "$BUILDSRC/why" -I "$BUILDSRC/av" -I "$BUILDSRC/../../src/why" -I "$BUILDSSRC/../../src/av"\
       $BUILDSRC/../../bin/astraver.byte $@
