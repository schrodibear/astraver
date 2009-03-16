
(* spec ? *)
val fold_term :
 ('a -> 'b Jc_ast.term -> 'a) -> 'a -> 'b Jc_ast.term -> 'a

(* spec ? *)
val iter_term : ('a Jc_ast.term -> unit) -> 'a Jc_ast.term -> unit

(* spec ? *)
val iter_term_and_assertion : 
  ('a Jc_ast.term -> unit) ->  ('a Jc_ast.assertion -> unit) 
  -> 'a Jc_ast.assertion -> unit

(* spec ? *)
val iter_location : 
  ('a Jc_ast.term -> unit) ->
  ('a Jc_ast.location -> unit) ->
  ('a Jc_ast.location_set -> unit) -> 'a Jc_ast.location -> unit

(* spec ? *)
val iter_expr_and_term_and_assertion :
  ('a Jc_ast.term -> unit) ->
  ('a Jc_ast.assertion -> unit) ->
  ('a Jc_ast.location -> unit) ->
  ('a Jc_ast.location_set -> unit) ->
  (('a, 'b) Jc_ast.expr -> unit) -> ('a, 'b) Jc_ast.expr -> unit
  

(* used only once in Jc_separation *)
val iter_funspec : 
  ('a Jc_ast.term -> unit) ->
  ('a Jc_ast.assertion -> unit) ->
  ('a Jc_ast.location -> unit) ->
  ('a Jc_ast.location_set -> unit) -> 'a Jc_ast.fun_spec -> unit

(* spec ? *)
val iter_pattern: (Jc_ast.pattern -> 'a) -> Jc_ast.pattern -> unit

(* spec ? *)
val map_term :
  (Jc_constructors.term_with -> Jc_fenv.logic_info Jc_ast.term) ->
  Jc_fenv.logic_info Jc_ast.term -> Jc_fenv.logic_info Jc_ast.term

(* spec ? *)
val map_term_in_assertion :
  (Jc_constructors.term_with -> Jc_fenv.logic_info Jc_ast.term) ->
  Jc_fenv.logic_info Jc_ast.assertion ->
  Jc_fenv.logic_info Jc_ast.assertion

(* spec ? *)
val fold_term : 
  ('a -> 'b Jc_ast.term -> 'a) -> 'a -> 'b Jc_ast.term -> 'a

(* spec ? *)
val fold_term_and_assertion :
  ('a -> 'b Jc_ast.term -> 'a) ->
  ('a -> 'b Jc_ast.assertion -> 'a) -> 'a -> 'b Jc_ast.assertion -> 'a

(* spec ? *)
val fold_rec_term : 
  ('a -> 'b Jc_ast.term -> bool * 'a) -> 'a -> 'b Jc_ast.term -> 'a

(* spec ? *)
val fold_rec_term_and_assertion :
  ('a -> 'b Jc_ast.term -> bool * 'a) ->
  ('a -> 'b Jc_ast.assertion -> bool * 'a) ->
  'a -> 'b Jc_ast.assertion -> 'a

(* spec ? *)
val fold_rec_location : 
  ('a -> 'b Jc_ast.term -> bool * 'a) ->
  ('a -> 'b Jc_ast.location -> bool * 'a) ->
  ('a -> 'b Jc_ast.location_set -> bool * 'a) ->
  'a -> 'b Jc_ast.location -> 'a

val fold_rec_expr_and_term_and_assertion : 
  ('a -> 'b Jc_ast.term -> bool * 'a) ->
  ('a -> 'b Jc_ast.assertion -> bool * 'a) ->
  ('a -> 'b Jc_ast.location -> bool * 'a) ->
  ('a -> 'b Jc_ast.location_set -> bool * 'a) ->
  ('a -> ('b, 'c) Jc_ast.expr -> bool * 'a) ->
  'a -> ('b, 'c) Jc_ast.expr -> 'a

val fold_rec_behavior: 
  ('a -> 'b Jc_ast.term -> bool * 'a) ->
  ('a -> 'b Jc_ast.assertion -> bool * 'a) ->
  ('a -> 'b Jc_ast.location -> bool * 'a) ->
  ('a -> 'b Jc_ast.location_set -> bool * 'a) ->
  'a -> 'b Jc_ast.behavior -> 'a

module IPExpr : sig

  (* spec ?
     This function is used only once, in Jc_norm 
     -> should be erased
  *)
  val fold_left : ('a -> Jc_ast.pexpr -> 'a) -> 'a -> Jc_ast.pexpr -> 'a

  (* Used twice in Jc_norm. spec ? *) 
  val subs : Jc_ast.pexpr -> Jc_ast.pexpr list

end

(* spec ? *)
val replace_sub_pexpr : 
    < node : Jc_ast.pexpr_node; pos : Loc.position; .. > ->
    Jc_ast.pexpr list -> Jc_constructors.pexpr_with

(* spec ?
   This function is used only once, in Jc_norm 
   -> should be erased
*)
val map_pexpr : 
  ?before:(Jc_ast.pexpr -> Jc_ast.pexpr) ->
  ?after:(Jc_constructors.pexpr_with -> Jc_constructors.pexpr_with) ->
  Jc_ast.pexpr -> Jc_ast.pexpr


module ITerm : sig
  type t = Jc_constructors.term
  val iter : (t -> unit) -> t -> unit
end

module INExpr : sig

  (* spec ? *)
  val subs: Jc_ast.nexpr -> Jc_ast.nexpr list
end

module IExpr : sig

  type t = Jc_constructors.expr

  (* spec ? *)
  val fold_left : ('a -> t -> 'a) -> 'a -> t -> 'a

end

