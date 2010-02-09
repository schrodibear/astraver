

(** {1 Frame ??} *)

val compute_needed_predicates: unit -> unit

val tr_logic_fun :
  Jc_fenv.logic_info ->
  Jc_fenv.logic_info Jc_ast.term_or_assertion ->
  Output.why_decl list -> Output.why_decl list


(*
  Local Variables: 
  compile-command: "unset LANG; make -j -C .. bin/jessie.byte"
  End: 
*)
