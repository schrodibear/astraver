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



(*s Identifiers. *)

module I : 
sig
  type t 
  val compare : t -> t -> int
end

type t = I.t

(* from :
       - string inform which creates the fresh ident
       - t list gives the arguments
*)
val create : ?from:(string * t list) -> string -> t

val string : t -> string

val completeString : t -> string 

val fresh_from : t -> (string * t list) option

module Idset : Set.S with type elt = t
type set = Idset.t

module Idmap : Map.S with type key = t
type 'a map = 'a Idmap.t

val next_away : t -> set -> t

val print : Format.formatter -> t -> unit
val lprint : Format.formatter -> t -> unit
val dbprint : Format.formatter -> t -> unit

(*s Possibly anonymous names *)

type name = Anonymous | Name of t

val print_name : Format.formatter -> name -> unit

(*s Qualified identifiers with labels. *)

val at_id : t -> string -> t
val un_at : t -> t * string
val is_at : t -> bool

(*s Bound variables. *)

val bound : t -> t

(*s Exceptions names and constructors *)

val exn_type : t
val exn_val : t
val exn_exn : t
val exn_post : t
val exn_qval : t
val exn_qexn : t
val exist : t
val decomp : int -> t

val exit_exn : t

val is_index : string -> bool

(*s Non termination monad. *)

val non_termination_monad : t
val nt_unit : t
val nt_bind : t
val nt_fix : t
val nt_lift : t

(*s Identifiers for the functional validation. *)

val fun_id : t -> t

(*s Identifiers for algebraic-typed term matching *)

val match_id : t -> t
val proj_id : t -> int -> t

(*s Some pre-defined identifiers. *)

val t_bool_and : t 
val t_bool_or : t
val t_bool_xor : t
val t_bool_not : t

val anonymous : t
val implicit : t
val default_post : t

val t_add : t
val t_sub : t
val t_mul : t
val t_div : t
val t_neg : t

val t_add_int : t
val t_sub_int : t
val t_mul_int : t
(* disabled (confusion math_div / computer_div)
val t_div_int : t
val t_mod_int : t
*)
val t_neg_int : t
val t_abs_int : t

val t_add_real : t
val t_sub_real : t
val t_mul_real : t
val t_div_real : t
val t_neg_real : t
val t_sqrt_real : t
val t_abs_real : t
val t_pow_real : t

val t_cos : t
val t_sin : t
val t_tan : t
val t_atan : t

val t_int_max : t
val t_int_min : t
val t_real_max : t
val t_real_min : t

val t_div_real_ : t
(* disabled (confusion math_div / computer_div)
val t_div_int_ : t
val t_mod_int_ : t
*)
val t_sqrt_real_ : t

val t_real_of_int : t
val t_int_of_real : t

val t_lt : t
val t_le : t
val t_gt : t
val t_ge : t
val t_eq : t
val t_neq : t

val t_eq_int : t
val t_eq_bool : t
val t_eq_real : t
val t_eq_unit : t

val t_neq_int : t
val t_neq_bool : t
val t_neq_real : t
val t_neq_unit : t

val t_lt_int : t
val t_le_int : t
val t_gt_int : t
val t_ge_int : t

val t_lt_real : t
val t_le_real : t
val t_gt_real : t
val t_ge_real : t

val t_lt_int_bool : t
val t_le_int_bool : t
val t_gt_int_bool : t
val t_ge_int_bool : t

val t_lt_real_bool : t
val t_le_real_bool : t
val t_gt_real_bool : t
val t_ge_real_bool : t

val t_eq_int_bool : t
val t_eq_real_bool : t
val t_neq_int_bool : t
val t_neq_real_bool : t

val t_eq_int_ : t
val t_eq_bool_ : t
val t_eq_real_ : t
val t_eq_unit_ : t

val t_neq_int_ : t
val t_neq_bool_ : t
val t_neq_real_ : t
val t_neq_unit_ : t

val t_lt_int_ : t
val t_le_int_ : t
val t_gt_int_ : t
val t_ge_int_ : t

val t_lt_real_ : t
val t_le_real_ : t
val t_gt_real_ : t
val t_ge_real_ : t

val t_distinct : t

val t_zwf_zero : t
val result : t
val default : t
val farray : t
val array_length : t
val if_then_else : t
val ref_set : t
val array_get : t
val array_set : t
val access : t
val store : t
val annot_bool : t
val well_founded : t
val well_founded_induction : t
val wfix : t
val false_rec : t

val any_int : t
val any_unit : t
val any_real : t

(*s Category tests *)

val is_wp : t -> bool
val is_variant : t -> bool

val is_poly : t -> bool

val is_comparison : t -> bool
val is_int_comparison : t -> bool
val is_real_comparison : t -> bool

val is_relation : t -> bool
val is_relation_ : t -> bool

val is_eq : t -> bool
val is_neq : t -> bool

val is_eq_ : t -> bool
val is_neq_ : t -> bool

val is_int_arith_binop : t -> bool
val is_int_arith_unop : t -> bool
val is_int_arith : t -> bool

val is_real_arith_binop : t -> bool
val is_real_arith : t -> bool

val is_arith_binop : t -> bool

val is_arith : t -> bool

val is_simplify_arith : t -> bool

val strict_bool_and_ : t
val strict_bool_or_ : t
val bool_not_ : t
