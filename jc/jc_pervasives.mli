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

open Jc_stdlib
open Jc_env
open Jc_envset
open Jc_ast
open Jc_fenv

val ( $ ): ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c

(*
exception Error of Loc.position * string

val error: Loc.position -> ('a, Format.formatter, unit, 'b) format4 -> 'a
*)

val zero: Num.num
val one: Num.num
val two: Num.num
val eight: Num.num
val is_power_of_two: Num.num -> bool
val log2: Num.num -> Num.num

(* labels *)

val new_label_name: unit -> string

(* types *)

val operator_of_native: native_type -> [> native_operator_type] 
val operator_of_type: jc_type -> [> operator_type] 
val eq_operator_of_type: jc_type -> [> operator_type] 

val integer_type : Jc_env.jc_type
val boolean_type : Jc_env.jc_type
val real_type : Jc_env.jc_type
val double_type : Jc_env.jc_type
val float_type : Jc_env.jc_type
val unit_type : Jc_env.jc_type
val null_type : Jc_env.jc_type
val string_type : Jc_env.jc_type
val any_type: jc_type

val string_of_native: Jc_env.native_type -> string
val print_type : Format.formatter -> Jc_env.jc_type -> unit
val print_type_var : Format.formatter -> Jc_env.type_var_info -> unit

val struct_of_union: Jc_env.struct_info -> bool
val struct_of_plain_union : Jc_env.struct_info -> bool
val struct_of_discr_union : Jc_env.struct_info -> bool
val union_of_field: Jc_env.field_info -> Jc_env.root_info
val integral_union: Jc_env.root_info -> bool
val root_is_plain_union : Jc_env.root_info -> bool
val root_is_discr_union : Jc_env.root_info -> bool
val root_is_union : Jc_env.root_info -> bool

val struct_has_bytesize: Jc_env.struct_info -> bool
val struct_bitsize: Jc_env.struct_info -> int
val struct_bytesize: Jc_env.struct_info -> int
val possible_struct_bytesize: Jc_env.struct_info -> int option

(* constants *)

val zero: Num.num
val num_of_constant : 'a -> const -> Num.num

(* environment infos *)

val var : ?unique:bool -> ?static:bool -> ?formal:bool -> 
  Jc_env.jc_type -> string -> Jc_env.var_info
val copyvar : Jc_env.var_info -> Jc_env.var_info

val tmp_var_name : unit -> string
val newvar : Jc_env.jc_type -> Jc_env.var_info
val newrefvar : Jc_env.jc_type -> Jc_env.var_info

val exception_info :  
  Jc_env.jc_type option -> string -> Jc_env.exception_info

val make_fun_info : string -> Jc_env.jc_type -> Jc_fenv.fun_info

val make_pred : string -> Jc_fenv.logic_info

val make_logic_fun : string -> Jc_env.jc_type -> Jc_fenv.logic_info

val location_set_region : location_set -> Jc_env.region
(*
val direct_embedded_struct_fields : Jc_env.struct_info -> Jc_env.field_info list
val embedded_struct_fields : Jc_env.struct_info -> Jc_env.field_info list
*)
val field_sinfo : Jc_env.field_info -> Jc_env.struct_info
val field_bounds : Jc_env.field_info -> Num.num * Num.num
(* destruct a pointer type. *)
val pointer_struct: jc_type -> struct_info
val pointer_class: jc_type -> pointer_class
(*val embedded_struct_roots : Jc_env.struct_info -> string list*)

val root_name : Jc_env.struct_info -> string
val field_root_name : Jc_env.field_info -> string
val struct_root : Jc_env.struct_info -> Jc_env.root_info
val pointer_class_root : pointer_class -> Jc_env.root_info

(* predefined functions *)

val any_string : Jc_fenv.logic_info
(*
val real_of_integer : Jc_fenv.logic_info
val real_of_integer_ : Jc_fenv.fun_info
*)
val full_separated : Jc_fenv.logic_info

val default_behavior : behavior

val empty_fun_effect : Jc_fenv.fun_effect
val empty_effects : Jc_fenv.effect

(* assertions *)

val skip_term_shifts :  term -> term
val skip_shifts : expr -> expr
val skip_tloc_range : location_set -> location_set

val select_option : 'a option -> 'a -> 'a
val is_constant_assertion : assertion -> bool

(* fun specs *)

val contains_normal_behavior : fun_spec -> bool
val contains_exceptional_behavior : fun_spec -> bool
val is_purely_exceptional_fun : fun_spec -> bool

(* patterns *)

(** The set of variables bound by a pattern. *)
val pattern_vars : Jc_env.var_info Jc_envset.StringMap.t -> pattern ->
  Jc_env.var_info Jc_envset.StringMap.t

(* operators *)

val string_of_op: [< bin_op | unary_op] -> string
val string_of_op_type: [< operator_type] -> string

(* builtin_logic_symbols *)

val builtin_logic_symbols :
  (Jc_env.jc_type option * string * string * Jc_env.jc_type list) list

val builtin_function_symbols :
  (Jc_env.jc_type * string * string * Jc_env.jc_type list * Jc_fenv.builtin_treatment) list

module TermOrd : OrderedHashedType with type t = term

module TermSet : Set.S with type elt = term

module TermMap : Map.S with type key = term

module TermTable : Hashtbl.S with type key = term

module AssertionOrd : OrderedType with type t = assertion

module StringHashtblIter:
sig
  type 'a t
  val create: int -> 'a t
  val add: 'a t -> string -> 'a -> unit
  val replace: 'a t -> string -> 'a -> unit
  val find: 'a t -> string -> 'a 
  val fold: (string -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val iter: (string -> 'a -> unit) -> 'a t -> unit
end

module IntHashtblIter:
sig
  type 'a t
  val create: int -> 'a t
  val add: 'a t -> int -> 'a -> unit
  val replace: 'a t -> int -> 'a -> unit
  val find: 'a t -> int -> 'a 
  val fold: (int -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val iter: (int -> 'a -> unit) -> 'a t -> unit
end

(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
