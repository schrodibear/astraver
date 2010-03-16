(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2010                                               *)
(*    INRIA (Institut National de Recherche en Informatique et en         *)
(*           Automatique)                                                 *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file licenses/LGPLv2.1).            *)
(*                                                                        *)
(**************************************************************************)


exception NotImplemented of string
exception Unsupported of string

val fatal          : ('a,Format.formatter,unit,'b) format4 -> 'a
val notimplemented : ('a,Format.formatter,unit,'b) format4 -> 'a
val unsupported    : ('a,Format.formatter,unit,'b) format4 -> 'a
val warning        : ('a,Format.formatter,unit) format -> 'a
val warn_general   : ('a,Format.formatter,unit) format -> 'a

(** warning for currently ignored feature which is only displayed once *)
val warn_once      : string -> unit

(* Jessie specific names *)

val name_of_default_behavior : string
val name_of_valid_wstring : string
val name_of_valid_string : string
val name_of_strlen : string
val name_of_wcslen : string

val name_of_hint_assertion : string
val name_of_string_declspec : string

val name_of_padding_type : string
val name_of_integral_type : ?bitsize:int -> Cil_types.typ -> string

val name_of_assert : string
val name_of_free : string
val name_of_malloc : string

val filter_alphanumeric : string -> (char * char) list -> char -> string

val type_name:  Cil_types.typ -> string

val logic_type_name:  Cil_types.logic_type -> string

(* unique names generation *)

val unique_name : string -> string

val unique_logic_name : string -> string

val unique_name_if_empty : string -> string


(* ????? *)

val checking : bool

val check_types : Cil_types.file -> unit

val integral_type_size_in_bits : Cil_types.typ -> int

val max_value_of_integral_type :
  ?bitsize:int -> Cil_types.typ -> Big_int.big_int

val min_value_of_integral_type :
  ?bitsize:int -> Cil_types.typ -> Big_int.big_int

val all_integral_types : (string, Cil_types.typ * int) Hashtbl.t

val term_of_var : Cil_types.varinfo -> Cil_types.term

val mkterm :
  Cil_types.term_node ->
  Cil_types.logic_type ->
  Lexing.position * Lexing.position -> Cil_types.term

val mkInfo : Cil_types.exp -> Cil_types.exp

val lift_offset : Cil_types.typ -> Cil_types.offset -> Cil_types.offset

val mkTRef : Cil_types.typ -> Cil_types.typ

val mkTRefArray :
  Cil_types.typ * Cil_types.exp * Cil_types.attributes ->
  Cil_types.typ

val mkalloc_statement : Cil_types.varinfo ->
           Cil_types.typ -> Cil_types.location -> Cil_types.stmt

val mkalloc_array_statement :
  Cil_types.varinfo ->
  Cil_types.typ -> int64 -> Cil_types.location -> Cil_types.stmt

val mkfree_statement :
  Cil_types.varinfo ->
  Cil_types.location -> Cil_types.stmt

val mkfree: Cil_types.varinfo -> Cil_types.location -> Cil_types.instr

val mkStructEmpty : string -> Cil_types.compinfo

val mkStructSingleton :
  ?padding:int ->
  string -> string -> Cil_types.typ -> Cil_types.compinfo

val malloc_function : unit -> Cil_types.varinfo
val free_function : unit -> Cil_types.varinfo

val flatten_multi_dim_array :  bool ref

val reference_of_array : Cil_types.typ -> Cil_types.typ

val get_struct_info : Cil_types.typ -> Cil_types.compinfo

val get_struct_name : Cil_types.typ -> string

val force_app_term_type : (Cil_types.typ -> 'a) -> Cil_types.logic_type -> 'a

val app_term_type : (Cil_types.typ -> 'a) -> 'a -> Cil_types.logic_type -> 'a

val is_base_addr : Cil_types.term -> bool

val is_reference_type : Cil_types.typ -> bool

val is_array_reference_type : Cil_types.typ -> bool

val is_assert_function : Cil_types.varinfo -> bool
val is_free_function : Cil_types.varinfo -> bool
val is_malloc_function : Cil_types.varinfo -> bool
val is_realloc_function : Cil_types.varinfo -> bool
val is_calloc_function : Cil_types.varinfo -> bool

val reference_size : Cil_types.typ -> int64

val bits_sizeof : Cil_types.typ -> int64

val is_unknown_location : Lexing.position * 'a -> bool

val get_unique_field : Cil_types.typ -> Cil_types.fieldinfo

val is_last_offset : Cil_types.offset -> bool

val struct_type_for_void : Cil_types.typ ref

val filter_alphanumeric : string -> (char * char) list -> char -> string

(*
val attach_globinit : Cil_types.stmt -> unit
*)

val attach_global : Cil_types.global -> unit

val attach_globaction : (unit -> unit) -> unit

val do_on_term :
  (Cil_types.exp -> Cil_types.exp) option *
  (Cil_types.exp -> Cil_types.exp) option ->
  Cil_types.term -> Cil_types.term Cil.visitAction

val do_on_term_offset :
  (Cil_types.offset -> Cil_types.offset) option *
  (Cil_types.offset -> Cil_types.offset) option ->
  Cil_types.term_offset -> Cil_types.term_offset Cil.visitAction

val do_on_term_lval :
  (Cil_types.lval -> Cil_types.lval) option *
  (Cil_types.lval -> Cil_types.lval) option ->
  Cil_types.term_lval -> Cil_types.term_lval Cil.visitAction

val do_and_update_globals  : (Cil_types.file -> 'a) -> Cil_types.file -> unit

val visit_and_update_globals :
  Visitor.frama_c_visitor -> Cil_types.file -> unit

val signal_change : unit -> unit

val almost_integer_type : Cil_types.typ

val add_pending_statement :  beginning:bool -> Cil_types.stmt -> unit

val visit_until_convergence :
  Visitor.frama_c_visitor -> Cil_types.file -> unit

type proxy_frama_c_visitor = Visitor.frama_c_visitor

val visit_and_push_statements_visitor :
  Visitor.frama_c_visitor -> proxy_frama_c_visitor

val visit_and_push_statements :
  (proxy_frama_c_visitor -> 'a -> 'b) ->
  Visitor.frama_c_visitor -> 'a -> 'b


val print_to_stdout : Cil_types.file -> unit
