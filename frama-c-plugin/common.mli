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


exception Unsupported of string

val jessie_emitter: Emitter.emitter

val fatal          : ('a,Format.formatter,unit,'b) format4 -> 'a
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
val name_of_kmalloc : string

val name_of_nondet_int : string ref

val filter_alphanumeric : string -> (char * char) list -> char -> string

val string_explode : string -> char list
val string_implode : char list -> string

val type_name:  Cil_types.typ -> string

val logic_type_name:  Cil_types.logic_type -> string

(* unique names generation *)

val unique_name : ?force:bool -> string -> string

val unique_logic_name : string -> string

val unique_name_if_empty : string -> string


(* ????? *)

val checking : unit -> bool

val check_types : Cil_types.file -> unit

val integral_type_size_in_bits : Cil_types.typ -> int

val promote_argument_type : Cil_types.typ -> Cil_types.typ

val max_value_of_integral_type :
  ?bitsize:int -> Cil_types.typ -> Integer.t

val min_value_of_integral_type :
  ?bitsize:int -> Cil_types.typ -> Integer.t

(* iter over existing integral types in alphabetical order. *)
val iter_integral_types: (string -> Cil_types.typ -> int option -> unit) -> unit

(* fold over existing integral types in alphabetical order. *)
val fold_integral_types:
  (string -> Cil_types.typ -> int option -> 'a -> 'a) -> 'a -> 'a

val term_of_var : Cil_types.varinfo -> Cil_types.term

val mkterm :
  Cil_types.term_node ->
  Cil_types.logic_type ->
  Lexing.position * Lexing.position -> Cil_types.term

val mkInfo : Cil_types.exp -> Cil_types.exp

val lift_offset : Cil_types.typ -> Cil_types.offset -> Cil_types.offset

val mkTRef : Cil_types.typ -> string -> Cil_types.typ

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

val (%) : ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c

val is_base_addr : Cil_types.term -> bool

val is_reference_type : Cil_types.typ -> bool

val is_array_reference_type : Cil_types.typ -> bool

val is_assert_function : Cil_types.varinfo -> bool
val is_free_function : Cil_types.varinfo -> bool
val is_kfree_function : Cil_types.varinfo -> bool
val is_special_free_function : Cil_types.varinfo -> bool
val is_malloc_function : Cil_types.varinfo -> bool
val is_kmalloc_function : Cil_types.varinfo -> bool
val is_kzalloc_function : Cil_types.varinfo -> bool
val is_realloc_function : Cil_types.varinfo -> bool
val is_calloc_function : Cil_types.varinfo -> bool

val blockfuns_include_file_name : string

val reference_size : Cil_types.typ -> int64

val bits_sizeof : Cil_types.typ -> int64

val is_unknown_location : Lexing.position * 'a -> bool

val get_unique_field : Cil_types.typ -> Cil_types.fieldinfo

val is_last_offset : Cil_types.offset -> bool

val struct_type_for_void : Cil_types.typ ref

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

class proxy_frama_c_visitor:  Visitor.frama_c_visitor -> Visitor.frama_c_visitor

val visit_and_push_statements_visitor :
  Visitor.frama_c_visitor -> proxy_frama_c_visitor

val visit_and_push_statements :
  (proxy_frama_c_visitor -> 'a -> 'b) ->
  Visitor.frama_c_visitor -> 'a -> 'b


val print_to_stdout : Cil_types.file -> unit

val constant_expr : ?loc:Cil_datatype.Location.t -> Integer.t -> Cil_types.exp


open Cil_types

type opaque_term_env = {
  term_lhosts: term_lhost Cil_datatype.Varinfo.Map.t;
  terms: term Cil_datatype.Varinfo.Map.t;
  vars: logic_var Cil_datatype.Varinfo.Map.t;
}

type opaque_exp_env = { exps: exp Cil_datatype.Varinfo.Map.t }

val force_term_to_exp: term -> exp * opaque_term_env
val force_back_exp_to_term: opaque_term_env -> exp -> term
val force_exp_to_term: exp -> term
val force_lval_to_term_lval: lval -> term_lval
val force_term_offset_to_offset: term_offset -> offset * opaque_term_env
val force_back_offset_to_term_offset: opaque_term_env -> offset -> term_offset
val force_exp_to_predicate: exp -> predicate named
val force_exp_to_assertion: exp -> code_annotation
val force_term_lval_to_lval: term_lval -> lval * opaque_term_env
val force_back_lval_to_term_lval: opaque_term_env -> lval -> term_lval

val drop : int -> 'a list -> 'a list
val take : int -> 'a list -> 'a list

val predicate: location -> predicate -> predicate named

module Trie : sig

  (* GPL-licensed OCaml trie implementation from https://www.lri.fr/~filliatr/ftp/ocaml/ds/trie.ml.html *)

  (**************************************************************************)
  (*                                                                        *)
  (*  Copyright (C) Jean-Christophe Filliatre                               *)
  (*                                                                        *)
  (*  This software is free software; you can redistribute it and/or        *)
  (*  modify it under the terms of the GNU Library General Public           *)
  (*  License version 2.1, with the special exception on linking            *)
  (*  described in file LICENSE.                                            *)
  (*                                                                        *)
  (*  This software is distributed in the hope that it will be useful,      *)
  (*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
  (*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
  (*                                                                        *)
  (**************************************************************************)

  (** This module implements {\em tries}. Given a map [M] over an
      arbitrary type [M.key], the following functor constructs a new map
      over type [M.key list]. *)

  module type Map = sig
    type key
    type +'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val find : key -> 'a t -> 'a
    val remove : key -> 'a t -> 'a t
    val mem : key -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  end

  module type S = sig
    type key
    type +'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val add : 'a t -> key list -> 'a -> 'a t
    val find_exn : 'a t -> key list -> 'a
    val find_all : 'a t -> key list -> 'a list
    val find_all2 : 'a t -> key list -> (key list * 'a) list
    val remove : 'a t -> key list -> 'a t
    val remove_all : 'a t -> key list -> 'a t
    val mem : 'a t -> key list -> bool
    val mem_any : 'a t -> key list -> bool
    val iter : (key list -> 'a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key list -> 'a -> 'b) -> 'a t -> 'b t
    val fold : (key list -> 'a -> 'b -> 'b) -> 'b -> 'a t -> 'b
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  end

  module Make(M : Map) : (S with type key := M.key)
end

module StringTrie : Trie.S with type key = char
module Int64Trie : Trie.S with type key = int64
