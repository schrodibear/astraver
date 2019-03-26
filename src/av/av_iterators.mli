(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
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

type term_subst = Fenv.term Envset.VarMap.t

val subst_term : term_subst -> Fenv.term -> Fenv.term

(* {2 miscellaneous} *)

(* spec ? *)
val fold_term :
 ('a -> 'b Ast.term -> 'a) -> 'a -> 'b Ast.term -> 'a

(* spec ? *)
val fold_term_in_assertion :
  ('a -> 'b Ast.term -> 'a) -> 'a -> 'b Ast.assertion -> 'a

(* spec ? *)
val iter_term : ('a Ast.term -> unit) -> 'a Ast.term -> unit

(* spec ? *)
val iter_term_and_assertion : 
  ('a Ast.term -> unit) ->  ('a Ast.assertion -> unit) 
  -> 'a Ast.assertion -> unit

(* spec ? *)
val iter_location : 
  ('a Ast.term -> unit) ->
  ('a Ast.location -> unit) ->
  ('a Ast.location_set -> unit) -> 'a Ast.location -> unit

(* spec ? *)
val iter_expr_and_term_and_assertion :
  ('a Ast.term -> unit) ->
  ('a Ast.assertion -> unit) ->
  ('a Ast.location -> unit) ->
  ('a Ast.location_set -> unit) ->
  (('a, 'b) Ast.expr -> unit) -> ('a, 'b) Ast.expr -> unit
  

(* used only once in Separation *)
val iter_funspec : 
  ('a Ast.term -> unit) ->
  ('a Ast.assertion -> unit) ->
  ('a Ast.location -> unit) ->
  ('a Ast.location_set -> unit) -> 'a Ast.fun_spec -> unit

val fold_funspec: ('a -> 'b Ast.term -> 'a) ->
                  ('a ->'b Ast.assertion -> 'a) ->
                  ('a ->'b Ast.location ->'a) ->
                  ('a ->'b Ast.location_set -> 'a) ->
                  'a -> 'b Ast.fun_spec -> 'a

(* spec ? *)
val iter_pattern: (Ast.pattern -> 'a) -> Ast.pattern -> unit

(* spec ? *)
val map_term :
  (Constructors.term_with -> Fenv.logic_info Ast.term) ->
  Fenv.logic_info Ast.term -> Fenv.logic_info Ast.term

(* spec ? *)
val map_term_in_assertion :
  (Constructors.term_with -> Fenv.logic_info Ast.term) ->
  Fenv.logic_info Ast.assertion ->
  Fenv.logic_info Ast.assertion

val map_assertion :
  (Constructors.assertion_with -> Fenv.logic_info Ast.assertion) ->
  Fenv.logic_info Ast.assertion -> Fenv.logic_info Ast.assertion

val map_term_and_assertion :
  (Constructors.assertion_with -> Fenv.logic_info Ast.assertion) ->
  (Constructors.term_with -> Fenv.logic_info Ast.term) ->
  Fenv.logic_info Ast.assertion -> Fenv.logic_info Ast.assertion

(* spec ? *)
val fold_term : 
  ('a -> 'b Ast.term -> 'a) -> 'a -> 'b Ast.term -> 'a

(* spec ? *)
val fold_term_and_assertion :
  ('a -> 'b Ast.term -> 'a) ->
  ('a -> 'b Ast.assertion -> 'a) -> 'a -> 'b Ast.assertion -> 'a

(* spec ? *)
val fold_rec_term : 
  ('a -> 'b Ast.term -> bool * 'a) -> 'a -> 'b Ast.term -> 'a

(* spec ? *)
val fold_rec_term_and_assertion :
  ('a -> 'b Ast.term -> bool * 'a) ->
  ('a -> 'b Ast.assertion -> bool * 'a) ->
  'a -> 'b Ast.assertion -> 'a

(* spec ? *)
val fold_rec_location : 
  ('a -> 'b Ast.term -> bool * 'a) ->
  ('a -> 'b Ast.location -> bool * 'a) ->
  ('a -> 'b Ast.location_set -> bool * 'a) ->
  'a -> 'b Ast.location -> 'a

val fold_rec_expr_and_term_and_assertion : 
  ('a -> 'b Ast.term -> bool * 'a) ->
  ('a -> 'b Ast.assertion -> bool * 'a) ->
  ('a -> 'b Ast.location -> bool * 'a) ->
  ('a -> 'b Ast.location_set -> bool * 'a) ->
  ('a -> ('b, 'c) Ast.expr -> bool * 'a) ->
  'a -> ('b, 'c) Ast.expr -> 'a

(*
val fold_rec_behavior: 
  ('a -> 'b Ast.term -> bool * 'a) ->
  ('a -> 'b Ast.assertion -> bool * 'a) ->
  ('a -> 'b Ast.location -> bool * 'a) ->
  ('a -> 'b Ast.location_set -> bool * 'a) ->
  'a -> 'b Ast.behavior -> 'a
*)

module IPExpr : sig

  (* spec ?
     This function is used only once, in Norm 
     -> should be erased
  *)
  val fold_left : ('a -> Ast.pexpr -> 'a) -> 'a -> Ast.pexpr -> 'a

  (* Used twice in Norm. spec ? *) 
  val subs : Ast.pexpr -> Ast.pexpr list

end

(* spec ? *)
val replace_sub_pexpr : 
    < node : Ast.pexpr_node; pos : Why_loc.position; .. > ->
    Ast.pexpr list -> Constructors.pexpr_with

(* spec ?
   This function is used only once, in Norm 
   -> should be erased
*)
val map_pexpr : 
  ?before:(Ast.pexpr -> Ast.pexpr) ->
  ?after:(Constructors.pexpr_with -> Constructors.pexpr_with) ->
  Ast.pexpr -> Ast.pexpr


(* spec ?
   This function is used only once, in Annot_inference
   -> should be erased
*)
val map_expr :
  ?before:((Fenv.logic_info, Fenv.fun_info) Ast.expr ->
             (Fenv.logic_info, Fenv.fun_info) Ast.expr) ->
  ?after:(Constructors.expr_with -> Constructors.expr_with) ->
  (Fenv.logic_info, Fenv.fun_info) Ast.expr ->
  (Fenv.logic_info, Fenv.fun_info) Ast.expr

val replace_sub_expr :
  < mark : string; node : Fenv.expr_node;
  original_type : Env.jc_type; pos : Why_loc.position;
  region : Env.region; typ : Env.jc_type; .. > ->
    (Fenv.logic_info, Fenv.fun_info) Ast.expr list ->
    Constructors.expr_with


module ITerm : sig
  type t = Constructors.term
  val iter : (t -> unit) -> t -> unit
end

module INExpr : sig

  (* spec ? *)
  val subs: Ast.nexpr -> Ast.nexpr list
end

module IExpr : sig

  type t = Constructors.expr

  (* spec ? *)
  val fold_left : ('a -> t -> 'a) -> 'a -> t -> 'a

  val subs : t -> t list 

end


(*
Local Variables: 
compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
End: 
*)
