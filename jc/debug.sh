#/bin/bash

DIR=$(dirname $(readlink -f $0))

ocamlc -c -I "$DIR/../src/" -o "$DIR/jc_debug_output.cmo" "$DIR/jc_debug_output.ml"

{
  echo "load_printer nums.cma"
  echo "load_printer pp.cmo"
  echo "load_printer jc_stdlib.cmo"
  echo "load_printer jc_envset.cmo"
  echo "load_printer option_misc.cmo"
  echo "load_printer jc_common_options.cmo"
  echo "load_printer jc_region.cmo"
  echo "load_printer jc_fenv.cmo"
  echo "load_printer loc.cmo"
  echo "load_printer jc_constructors.cmo"
  echo "load_printer jc_pervasives.cmo"
  echo "load_printer jc_output_misc.cmo"
  echo "load_printer jc_iterators.cmo"
  echo "load_printer jc_type_var.cmo"
  echo "load_printer jc_poutput.cmo"
  echo "load_printer jc_output.cmo"
  echo "load_printer jc_debug_output.cmo"
  echo "install_printer Jc_debug_output.expr"
  echo "install_printer Jc_debug_output.assertion"
  echo "install_printer Jc_debug_output.term"
  cat
} |
rlwrap ocamldebug -I "$DIR/../src/" -I "$DIR" $@