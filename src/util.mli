(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(*i $Id: util.mli,v 1.26 2002-10-31 12:27:00 filliatr Exp $ i*)

open Logic
open Misc
open Types
open Ast
open Env

val erase_label : string -> predicate -> predicate
val change_label : string -> string -> predicate -> predicate
val put_label_term : local_env -> string -> term -> term

val traverse_binders : local_env -> (type_v binder) list -> local_env
val initial_renaming : local_env -> Rename.t

val apply_term : Rename.t -> local_env -> term -> term
val apply_pre : Rename.t -> local_env -> precondition -> precondition
val apply_assert : Rename.t -> local_env -> assertion -> assertion
val apply_post : 
  label -> Rename.t -> local_env -> postcondition -> postcondition

val is_reference : local_env -> Ident.t -> bool
val predicate_now_refs : local_env -> predicate -> Ident.set
val predicate_refs : local_env -> predicate -> Ident.set
val term_now_refs : local_env -> term -> Ident.set
val term_refs : local_env -> term -> Ident.set
val post_refs : local_env -> postcondition -> Ident.set

val deref_type : type_v -> type_v
val dearray_type : type_v -> term * type_v

val decomp_kappa : type_c -> 
  (Ident.t * type_v) * Effect.t * precondition list * postcondition option

val equality : term -> term -> predicate

val decomp_boolean : postcondition option -> predicate * predicate

val effect : typed_program -> Effect.t
val pre : typed_program -> precondition list
val post : typed_program -> postcondition option
val result_type : typed_program -> type_v
val result_name : typing_info -> Ident.t

val erase_exns : typing_info -> typing_info

val forall : Ident.t -> type_v -> predicate -> predicate
val foralls : (Ident.t  * type_v) list -> predicate -> predicate

val exists : Ident.t -> type_v -> predicate -> predicate

(*s Occurrences *)

val occur_term : Ident.t -> term -> bool
val occur_predicate : Ident.t -> predicate -> bool
val occur_assertion : Ident.t -> assertion -> bool
val occur_post : Ident.t -> postcondition option -> bool
val occur_type_v : Ident.t -> type_v -> bool
val occur_type_c : Ident.t -> type_c -> bool

(*s Functions to translate array operations *)

val array_info : 
  local_env -> Ident.t -> term * type_v

val make_raw_access :
  local_env -> Ident.t * Ident.t -> term -> term

val make_raw_store :
  local_env -> Ident.t * Ident.t -> term -> term -> term

val make_pre_access :
  local_env -> Ident.t -> term -> predicate

(*s Pretty printers. *)

open Format

val print_pred_binders : bool ref

val print_pure_type : formatter -> pure_type -> unit
val print_logic_type : formatter -> logic_type -> unit
val print_type_v : formatter -> type_v -> unit
val print_type_c : formatter -> type_c -> unit
val print_prog : formatter -> typed_program -> unit
val print_cc_term : formatter -> predicate Cc.cc_term -> unit
val print_cc_pattern : formatter -> Cc.cc_pattern -> unit

val print_subst : formatter -> substitution -> unit
val print_cc_subst : formatter -> predicate Cc.cc_term Ident.map -> unit

val print_env : Format.formatter -> local_env -> unit
