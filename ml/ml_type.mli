(** Add a type declaration like [type t = ...] so that type [t] is known and
can be instanciated. *)
val declare: Ml_ocaml.Ident.t -> Ml_ocaml.Types.type_declaration -> bool -> unit

(** Add an invariant to a declared type. *)
val add_invariant: Ml_ocaml.Ident.t ->
  (string * Jc_env.var_info * Jc_ast.assertion) -> unit

(** Translate an OCaml type into a Jessie type. May instanciate the type if
needed. *)
val make: Ml_ocaml.Types.type_expr -> Jc_env.jc_type

(** If the argument is a record type or a tuple, return the structure used
to interpret it. Fail otherwise. *)
val structure: Ml_ocaml.Types.type_expr -> Jc_env.struct_info

type ml_label_info = {
  ml_li_name: string;
  ml_li_structure: Jc_env.struct_info;
  ml_li_field: Jc_env.field_info;
}

(** Given a record type and a label of this record, instantiate the type if
needed and return the label interpretation. *)
val label: Ml_ocaml.Types.type_expr -> Ml_ocaml.Types.label_description ->
  ml_label_info

type ml_constructor_info = {
  ml_ci_name: string;
  ml_ci_structure: Jc_env.struct_info;
  ml_ci_arguments: Jc_env.field_info list;
}

(** Given a variant type and a tag of this record, instantiate the type if
needed and return the tag interpretation. *)
val constructor: Ml_ocaml.Types.type_expr -> 
  Ml_ocaml.Types.constructor_description -> ml_constructor_info

(** Return the field associated to some tuple projection. *)
val proj: Ml_ocaml.Types.type_expr -> int -> Jc_env.field_info

(** Return the declarations for all type instantiations. *)
val jc_decls: unit -> Jc_output.jc_decl list

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.opt"
End: 
*)
