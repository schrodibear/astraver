type t

val empty: t

val add_var: string -> Jc_env.jc_type -> t -> t
val add_fun: string -> Jc_env.var_info list -> Jc_env.jc_type -> t -> t
val add_spec: Ml_ocaml.Ident.t -> Ml_ocaml.Typedtree.function_spec -> t -> t
val add_field: string -> Jc_env.jc_type -> Jc_env.struct_info -> t ->
  t * Jc_env.field_info
val add_struct: Jc_env.struct_info -> t -> t

val find_var: string -> t -> Jc_env.var_info
val find_fun: string -> t -> Jc_fenv.fun_info
val find_spec: Ml_ocaml.Ident.t -> t -> Ml_ocaml.Typedtree.function_spec
val find_field: string -> t -> Jc_env.field_info
val find_struct: string -> t -> Jc_env.struct_info

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.byte"
End: 
*)
