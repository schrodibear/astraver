(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: ident.mli,v 1.54 2006-11-21 22:02:26 filliatr Exp $ i*)

(*s Identifiers. *)

type t

val create : string -> t

val string : t -> string

val completeString : t -> string 

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

(*s Some pre-defined identifiers. *)

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
val t_div_int : t
val t_mod_int : t
val t_neg_int : t

val t_add_real : t
val t_sub_real : t
val t_mul_real : t
val t_div_real : t
val t_neg_real : t
val t_sqrt_real : t
val t_abs_real : t
val t_pow_real : t

val t_div_real_ : t
val t_div_int_ : t
val t_mod_int_ : t
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
