(** Interpretation of patterns. *)

(** Translate an OCaml pattern to a Jessie pattern. Return the environment
extended with the variables bound by the pattern. *)
val pattern: Ml_env.t -> Ml_ocaml.Typedtree.pattern -> Ml_env.t * Jc_ast.pattern

(** Translate an OCaml pattern to a Jessie pattern-matching term with
a single case.
The second argument is used to get the body of the pattern; its argument is
the environment in which the body should be typed (with the variables bound
by the pattern).
Return value is [vi, t] where [vi] is a Jc_env.var_info which should be bound
to the argument of the pattern-matching. *)
val pattern_term: Ml_env.t -> (Ml_env.t -> Jc_ast.term) ->
  Ml_ocaml.Typedtree.pattern -> Jc_env.var_info * Jc_ast.term

(** Same as [pattern_term] but with a list of arguments instead. *)
val pattern_list_term: Ml_env.t -> (Ml_env.t -> Jc_ast.term) ->
  Ml_ocaml.Typedtree.pattern list -> Jc_env.var_info list * Jc_ast.term

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.opt"
End: 
*)
