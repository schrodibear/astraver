(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: util.mli,v 1.10 2002-03-11 11:46:23 filliatr Exp $ i*)

open Logic
open Misc
open Types
open Ast
open Env

val make_before_after : predicate -> predicate
val make_after_before : local_env -> predicate -> predicate
val make_after_before_term : local_env -> term -> term
val erase_label : string -> predicate -> predicate
val change_label : string -> string -> predicate -> predicate

val traverse_binders : local_env -> (type_v binder) list -> local_env
val initial_renaming : local_env -> Rename.t

val apply_term : Rename.t -> local_env -> term -> term
val apply_pre : Rename.t -> local_env -> precondition -> precondition
val apply_post : Rename.t -> local_env -> string -> postcondition ->
  postcondition
val apply_assert : Rename.t -> local_env -> assertion -> assertion

val type_v_subst : (Ident.t * Ident.t) list -> type_v -> type_v
val type_c_subst : (Ident.t * Ident.t) list -> type_c -> type_c

val type_v_rsubst : (Ident.t * term) list -> type_v -> type_v
val type_c_rsubst : (Ident.t * term) list -> type_c -> type_c

val type_c_of_v : type_v -> type_c
val make_arrow : type_v binder list -> type_c -> type_v

val is_reference : local_env -> Ident.t -> bool
val predicate_now_refs : local_env -> predicate -> Ident.set
val predicate_refs : local_env -> predicate -> Ident.set
val term_now_vars : local_env -> term -> Ident.set

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

val print_type_v : formatter -> type_v -> unit
val print_type_c : formatter -> type_c -> unit
val print_prog : formatter -> typed_program -> unit
val print_cc_term : formatter -> cc_term -> unit
