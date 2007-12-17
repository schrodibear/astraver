val declare: Ml_ocaml.Ident.t -> Ml_ocaml.Types.type_declaration -> unit

val add_invariant: Ml_ocaml.Ident.t ->
  (string * Jc_env.var_info * Jc_ast.assertion) -> unit

val make: Ml_ocaml.Types.type_expr -> Jc_env.jc_type

val structure: Ml_ocaml.Types.type_expr -> Jc_env.struct_info

type ml_label_info = {
  ml_li_name: string;
  ml_li_structure: Jc_env.struct_info;
  ml_li_field: Jc_env.field_info;
}

val label: Ml_ocaml.Types.type_expr -> Ml_ocaml.Types.label_description ->
  ml_label_info

type ml_constructor_info = {
  ml_ci_name: string;
  ml_ci_tag: int;
  ml_ci_structure: Jc_env.struct_info;
  ml_ci_tag_field: Jc_env.field_info;
  ml_ci_arguments: Jc_env.field_info list;
}

val constructor: Ml_ocaml.Types.type_expr -> 
  Ml_ocaml.Types.constructor_description -> ml_constructor_info

val jc_decls: unit -> Jc_output.jc_decl list

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.opt"
End: 
*)
