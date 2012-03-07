(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* {1 substitution in logic} *)

type term_subst = Jc_fenv.term Jc_envset.VarMap.t

val subst_term : term_subst -> Jc_fenv.term -> Jc_fenv.term

(* {2 miscellaneous} *)

(* spec ? *)
val fold_term :
 ('a -> 'b Jc_ast.term -> 'a) -> 'a -> 'b Jc_ast.term -> 'a

(* spec ? *)
val fold_term_in_assertion :
  ('a -> 'b Jc_ast.term -> 'a) -> 'a -> 'b Jc_ast.assertion -> 'a

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

(*
val fold_rec_behavior: 
  ('a -> 'b Jc_ast.term -> bool * 'a) ->
  ('a -> 'b Jc_ast.assertion -> bool * 'a) ->
  ('a -> 'b Jc_ast.location -> bool * 'a) ->
  ('a -> 'b Jc_ast.location_set -> bool * 'a) ->
  'a -> 'b Jc_ast.behavior -> 'a
*)

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


(* spec ?
   This function is used only once, in Jc_annot_inference
   -> should be erased
*)
val map_expr :
  ?before:((Jc_fenv.logic_info, Jc_fenv.fun_info) Jc_ast.expr ->
             (Jc_fenv.logic_info, Jc_fenv.fun_info) Jc_ast.expr) ->
  ?after:(Jc_constructors.expr_with -> Jc_constructors.expr_with) ->
  (Jc_fenv.logic_info, Jc_fenv.fun_info) Jc_ast.expr ->
  (Jc_fenv.logic_info, Jc_fenv.fun_info) Jc_ast.expr

val replace_sub_expr :
  < mark : string; node : Jc_fenv.expr_node;
  original_type : Jc_env.jc_type; pos : Loc.position;
  region : Jc_env.region; typ : Jc_env.jc_type; .. > ->
    (Jc_fenv.logic_info, Jc_fenv.fun_info) Jc_ast.expr list ->
    Jc_constructors.expr_with


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

  val subs : t -> t list 

end


(*
Local Variables: 
compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
End: 
*)
