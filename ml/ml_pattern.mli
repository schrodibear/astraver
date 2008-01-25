(** Interpretation of patterns. *)

val pattern: Ml_env.t -> Ml_ocaml.Typedtree.pattern -> Ml_env.t * Jc_ast.pattern

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.opt"
End: 
*)
