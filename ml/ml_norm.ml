open Ml_misc
open Ml_ocaml.Typedtree
open Ml_ast

let structure_item env = function
  | Tstr_value(r, pel) -> JTstr_value(r, assert false)
  | _ -> not_implemented Ml_ocaml.Location.none "ml_norm.structure_item"

let structure env = List.map (structure_item env)


(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.byte"
End: 
*)
