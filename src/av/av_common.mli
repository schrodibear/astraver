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

open Stdlib
open Env
open Envset
open Ast
open Fenv

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

val integer_type : Env.jc_type
val boolean_type : Env.jc_type
val real_type : Env.jc_type
val double_type : Env.jc_type
val float_type : Env.jc_type
val unit_type : Env.jc_type
val null_type : Env.jc_type
val string_type : Env.jc_type
val any_type: jc_type

val string_of_native: Env.native_type -> string
val string_of_some_enum : Env.some_enum -> string
val print_type : Format.formatter -> Env.jc_type -> unit
val print_type_var : Format.formatter -> Env.type_var_info -> unit

val struct_of_union: Env.struct_info -> bool
val struct_of_plain_union : Env.struct_info -> bool
val struct_of_discr_union : Env.struct_info -> bool
val union_of_field: Env.field_info -> Env.root_info
val integral_union: Env.root_info -> bool
val root_is_plain_union : Env.root_info -> bool
val root_is_discr_union : Env.root_info -> bool
val root_is_union : Env.root_info -> bool

(* constants *)

val zero: Num.num
val num_of_constant : 'a -> const -> Num.num

(* environment infos *)

val var : ?unique:bool -> ?static:bool -> ?formal:bool -> ?bound:bool -> Env.jc_type -> string -> Env.var_info
val copyvar : Env.var_info -> Env.var_info

val tmp_var_name : unit -> string
val newvar : Env.jc_type -> Env.var_info
val newrefvar : Env.jc_type -> Env.var_info

val exception_info :
  Env.jc_type option -> string -> Env.exception_info

val make_fun_info : string -> Env.jc_type -> Fenv.fun_info

val make_pred : string -> Fenv.logic_info

val make_logic_fun : string -> Env.jc_type -> Fenv.logic_info

val location_set_region : location_set -> Env.region
val location_set_of_location : location -> location_set
(*
val direct_embedded_struct_fields : Env.struct_info -> Env.field_info list
val embedded_struct_fields : Env.struct_info -> Env.field_info list
*)
val field_sinfo : Env.field_info -> Env.struct_info
val field_bounds : Env.field_info -> Num.num * Num.num
(* destruct a pointer type. *)
val pointer_struct: jc_type -> struct_info
val pointer_class: jc_type -> pointer_class
(*val embedded_struct_roots : Env.struct_info -> string list*)

val root_name : Env.struct_info -> string
val field_root_name : Env.field_info -> string
val struct_root : Env.struct_info -> Env.root_info
val pointer_class_root : pointer_class -> Env.root_info

(* predefined functions *)

val any_string : Fenv.logic_info
(*
val real_of_integer : Fenv.logic_info
val real_of_integer_ : Fenv.fun_info
*)
val full_separated : Fenv.logic_info

val default_behavior : behavior

val empty_fun_effect : Fenv.fun_effect
val empty_effects : Fenv.effect

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
val pattern_vars : Env.var_info Envset.StringMap.t -> pattern ->
  Env.var_info Envset.StringMap.t

(* operators *)

val string_of_op: [< bin_op | unary_op] -> string
val string_of_op_type: [< operator_type] -> string

(* builtin_logic_symbols *)

val builtin_logic_symbols :
  (Env.jc_type option * string * string * Env.jc_type list) list

val is_reinterpretation_predicate : logic_info -> bool

val builtin_function_symbols :
  (Env.jc_type * string * string * Env.jc_type list * Fenv.builtin_treatment) list

val builtin_enum_symbols : (string * Env.enum_info) list

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
  val mem: 'a t -> int -> bool
  val fold: (int -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val iter: (int -> 'a -> unit) -> 'a t -> unit
end

module Enum_info : sig
    val equal : ?by_name:bool -> enum_info -> enum_info -> bool
    val (=) : enum_info -> enum_info -> bool
end

(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
