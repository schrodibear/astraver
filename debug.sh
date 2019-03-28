#/bin/bash

DIR=$(dirname $(readlink -f $0))
BUILDSRC=$DIR/_build/default/src/av/.astraver.objs/byte/

make -C $DIR -j byte

SCRIPT='load_printer str.cma
load_printer nums.cma
load_printer astraver__Pp.cmo
load_printer astraver__Stdlib.cmo
load_printer astraver__Envset.cmo
load_printer astraver__Common_options.cmo
load_printer astraver__Region.cmo
load_printer astraver__Fenv.cmo
load_printer astraver__Loc.cmo
load_printer astraver__Constructors.cmo
load_printer astraver__Common.cmo
load_printer astraver__Print_misc.cmo
load_printer astraver__Iterators.cmo
load_printer astraver__Type_var.cmo
load_printer astraver__Print_p.cmo
load_printer astraver__Print.cmo
load_printer astraver__Debug_print.cmo

load_printer astraver__Print_n.cmo
load_printer astraver__Rc.cmo
load_printer astraver__Version.cmo
load_printer astraver__Position.cmo
load_printer astraver__Name.cmo
load_printer astraver__Output.cmo
load_printer astraver__Common_options.cmo
load_printer astraver__Options.cmo
load_printer astraver__Norm.cmo
load_printer astraver__Struct_tools.cmo
load_printer astraver__Typing.cmo
load_printer astraver__Effect.cmo

install_printer Astraver__Effect.print_effect
install_printer Astraver__Debug_print.expr
install_printer Astraver__Debug_print.assertion
install_printer Astraver__Debug_print.term
install_printer Astraver__Debug_print.string_set
install_printer Astraver__Debug_print.location
install_printer Astraver__Debug_print.location_set
set print_depth 3
'
rlwrap -P "$SCRIPT" ocamldebug -I "$BUILDSRC" -I "$DIR/src/av" $DIR/bin/astraver.byte $@
