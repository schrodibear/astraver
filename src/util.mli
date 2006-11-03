(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
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

(*i $Id: util.mli,v 1.52 2006-11-03 11:55:33 marche Exp $ i*)

open Logic
open Misc
open Types
open Ast
open Env

val erase_label : string -> predicate -> predicate
val change_label : string -> string -> predicate -> predicate
val put_label_term : local_env -> string -> term -> term
val put_label_predicate : local_env -> string -> predicate -> predicate

val traverse_binders : local_env -> (type_v binder) list -> local_env
val initial_renaming : local_env -> Rename.t

val apply_term : 
  Rename.t -> local_env -> term -> term
val apply_assert : 
  Rename.t -> local_env -> Types.assertion -> Types.assertion
val a_apply_assert : 
  Rename.t -> local_env -> assertion -> assertion
val apply_post : 
  label -> Rename.t -> local_env -> Types.postcondition -> Types.postcondition
val a_apply_post : 
  label -> Rename.t -> local_env -> postcondition -> postcondition

val oldify : local_env -> Effect.t -> term -> term
val type_c_subst_oldify : local_env -> Ident.t -> term -> type_c -> type_c

val is_reference : local_env -> Ident.t -> bool
val predicate_now_refs : local_env -> predicate -> Ident.set
val predicate_refs : local_env -> predicate -> Ident.set
val term_now_refs : local_env -> term -> Ident.set
val term_refs : local_env -> term -> Ident.set
val post_refs : local_env -> postcondition -> Ident.set

val deref_type : type_v -> pure_type
val dearray_type : type_v -> pure_type

val decomp_type_c : type_c -> 
  (Ident.t * type_v) * Effect.t * 
  Types.precondition list * Types.postcondition option
val decomp_kappa : typing_info -> 
  (Ident.t * type_v) * Effect.t * Ast.postcondition option

val equality : term -> term -> predicate
val tequality : type_v -> term -> term -> predicate

val decomp_boolean : postcondition -> predicate * predicate

val effect : typed_expr -> Effect.t
val post : typed_expr -> postcondition option
val result_type : typed_expr -> type_v
val result_name : typing_info -> Ident.t

val erase_exns : typing_info -> typing_info

val forall : 
  ?is_wp:is_wp -> Ident.t -> type_v -> ?triggers:triggers 
  -> predicate -> predicate
val foralls : ?is_wp:is_wp -> (Ident.t * type_v) list -> predicate -> predicate
val exists : Ident.t -> type_v -> predicate -> predicate

(* versions performing simplifcations *)
val pforall : ?is_wp:is_wp -> Ident.t -> type_v -> predicate -> predicate
val pexists : Ident.t -> type_v -> predicate -> predicate

(*s Occurrences *)

val occur_term : Ident.t -> term -> bool
val occur_predicate : Ident.t -> predicate -> bool
val occur_assertion : Ident.t -> assertion -> bool
val occur_post : Ident.t -> postcondition option -> bool
val occur_type_v : Ident.t -> type_v -> bool
val occur_type_c : Ident.t -> type_c -> bool

(*s Functions to translate array operations *)

val array_info : 
  local_env -> Ident.t -> pure_type

val make_raw_access :
  local_env -> Ident.t * Ident.t -> term -> term

val make_raw_store :
  local_env -> Ident.t * Ident.t -> term -> term -> term

val make_pre_access :
  local_env -> Ident.t -> term -> predicate

(*s AST builders for program transformation *)

val make_lnode : 
  Loc.position -> typing_info Ast.t_desc ->
  local_env -> type_c -> typed_expr
val make_var : 
  Loc.position -> Ident.t -> type_v -> local_env -> typed_expr
val make_expression :
  Loc.position -> term -> type_v -> local_env -> typed_expr
val make_annot_bool :
  Loc.position -> bool -> local_env -> typed_expr
val make_void :
  Loc.position -> local_env -> typed_expr
val make_raise :
  Loc.position -> Ident.t -> type_v -> local_env -> typed_expr

val change_desc : 'a Ast.t -> 'a Ast.t_desc -> 'a Ast.t

val force_post :
  local_env -> postcondition option -> typed_expr -> typed_expr

val create_postval : predicate -> assertion option

val create_post : predicate -> (assertion * 'b list) option

(*s Pretty printers. *)

open Format

val print_pred_binders : bool ref

val print_pure_type : formatter -> pure_type -> unit
val print_logic_type : formatter -> logic_type -> unit

val print_term : formatter -> term -> unit
val print_predicate : formatter -> predicate -> unit
val print_assertion : formatter -> assertion -> unit
val print_wp : formatter -> assertion option -> unit

val print_type_v : formatter -> type_v -> unit
val print_type_c : formatter -> type_c -> unit
val print_typing_info : formatter -> typing_info -> unit
val print_expr : formatter -> typed_expr -> unit

val print_cc_type : formatter -> Cc.cc_type -> unit
val print_cc_term : formatter -> ('a * predicate) Cc.cc_term -> unit
val print_cc_pattern : formatter -> Cc.cc_pattern -> unit

val print_subst : formatter -> substitution -> unit
val print_cc_subst : formatter -> ('a * predicate) Cc.cc_term Ident.map -> unit

val print_env : formatter -> local_env -> unit

val print_ptree : formatter -> Ptree.parsed_program -> unit
val print_pfile : formatter -> Ptree.decl list -> unit

val print_decl : formatter -> Logic_decl.t -> unit
