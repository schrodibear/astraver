module type TPatternArg = sig
  type t
  type expr
  type condition
  val make_if: condition -> t -> t -> t
  val make_if_expr: condition -> expr -> expr -> expr
  val make_var: Jc_env.var_info -> expr -> t -> t
  val make_equal: expr -> expr -> condition
  val make_and: condition -> condition -> condition
  val make_or: condition -> condition -> condition
  val make_deref: expr -> Jc_env.field_info -> expr
  val make_constant: Ml_ocaml.Asttypes.constant -> expr
  val make_bool: bool -> condition
  val make_int: int -> expr
end

module type TPattern = sig
  type t
  type expr
  type condition

  val pattern: Ml_env.t -> expr -> Ml_ocaml.Typedtree.pattern ->
    condition * Ml_env.t * (Jc_env.var_info * expr) list

  val pattern_expr: Ml_env.t -> expr -> Ml_ocaml.Typedtree.pattern ->
    (Ml_env.t -> t) -> condition * t

  val pattern_expr_list: Ml_env.t -> expr ->
    (Ml_ocaml.Typedtree.pattern * (Ml_env.t -> t)) list -> t option -> t

  val pattern_list: Ml_env.t -> expr list -> Ml_ocaml.Typedtree.pattern list ->
    condition * Ml_env.t * (Jc_env.var_info * expr) list

  val pattern_list_expr: Ml_env.t -> expr list ->
    Ml_ocaml.Typedtree.pattern list -> (Ml_env.t -> t) ->
    condition * Ml_env.t * t
end

module type TPatternF = functor (A: TPatternArg) -> TPattern
  with type t = A.t
  with type expr = A.expr
  with type condition = A.condition

module Pattern: TPatternF

module PatStatement: TPattern
  with type t = Jc_ast.tstatement
  with type expr = Jc_ast.texpr
  with type condition = Jc_ast.texpr

module PatExpression: TPattern
  with type t = Jc_ast.texpr
  with type expr = Jc_ast.texpr
  with type condition = Jc_ast.texpr

module PatAssertion: TPattern
  with type t = Jc_ast.assertion
  with type expr = Jc_ast.term
  with type condition = Jc_ast.term


(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.opt"
End: 
*)
