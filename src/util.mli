
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: util.mli,v 1.3 2001-08-19 02:44:48 filliatr Exp $ *)

open Logic
open Misc
open Types
open Ast
open Env

val is_mutable : type_v -> bool
val is_pure : type_v -> bool

val named_app : (predicate -> predicate) -> assertion -> assertion
val pre_app : (predicate -> predicate) -> precondition -> precondition
val post_app : (predicate -> predicate) -> postcondition -> postcondition

val anonymous : predicate -> assertion
val anonymous_pre : bool -> predicate -> precondition
val out_post : postcondition option -> predicate
val pre_of_assert : bool -> assertion -> precondition
val assert_of_pre : precondition -> assertion

val force_post_name : postcondition option -> postcondition option
val force_bool_name : postcondition option -> postcondition option

val make_before_after : predicate -> predicate

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

val make_arrow : type_v binder list -> type_c -> type_v

val is_mutable_in_env : local_env -> Ident.t -> bool
val predicate_now_vars : local_env -> predicate -> Ident.set
val term_now_vars : local_env -> term -> Ident.set

val deref_type : type_v -> type_v
val dearray_type : type_v -> term * type_v

val decomp_kappa : type_c -> 
  (Ident.t * type_v) * Effect.t * precondition list * postcondition option

(* Functions to translate array operations *)

val array_info : Rename.t -> local_env -> Ident.t -> term * type_v

val make_raw_access :
  Rename.t -> local_env -> Ident.t * Ident.t -> term -> term

val make_raw_store :
  Rename.t -> local_env -> Ident.t * Ident.t -> term -> term -> term

val make_pre_access :
  Rename.t -> local_env -> Ident.t -> term -> predicate

(* pretty printers *)

open Format

val print_type_v : formatter -> type_v -> unit
val print_type_c : formatter -> type_c -> unit
val print_cc_term : formatter -> cc_term -> unit
