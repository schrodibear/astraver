
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: monad.mli,v 1.3 2001-08-19 02:44:48 filliatr Exp $ *)

open Logic
open Types
open Ast
open Env

(* Main part of the translation of imperative programs into functional ones
 * (with mlise.ml) *)

(* Here we translate the specification into a CIC specification *)

val trad_ml_type_v : Rename.t -> local_env -> type_v -> cc_type
val trad_ml_type_c : Rename.t -> local_env -> type_c -> cc_type
val trad_imp_type  : Rename.t -> local_env -> type_v -> cc_type
val trad_type_in_env : Rename.t -> local_env -> Ident.t -> cc_type

val binding_of_alist : Rename.t -> local_env
                    -> (Ident.t * Ident.t) list
		    -> cc_binder list
val make_abs : cc_binder list -> cc_term -> cc_term
val abs_pre : Rename.t -> local_env -> cc_term * cc_type -> 
  precondition list -> cc_term

(* The following functions translate the main constructions *)

val result_tuple : Rename.t -> string -> local_env
          -> (Ident.t * cc_term * cc_type) -> (Effect.t * postcondition option)
          -> cc_term * cc_type

val let_in_pre : cc_type -> precondition -> cc_term -> cc_term

val make_let_in : Rename.t -> local_env -> cc_term 
          -> precondition list
          -> ((Ident.t * Ident.t) list * assertion option) 
	  -> Ident.t * type_v
	  -> cc_term * cc_type -> cc_term

val make_block : Rename.t -> local_env
          -> (Rename.t -> (Ident.t * type_v) option -> cc_term * cc_type)
	  -> (cc_term * type_c) block
	  -> cc_term

val make_app : local_env
          -> Rename.t -> (cc_term * type_c) list
	  -> Rename.t -> cc_term * type_c
	  -> ((type_v binder list) * type_c)
	    * ((Ident.t * Ident.t) list)
	    * type_c
	  -> type_c
          -> cc_term

val make_if : Rename.t -> local_env 
         -> cc_term * type_c
	 -> Rename.t
         -> cc_term * type_c
         -> cc_term * type_c
         -> type_c
         -> cc_term

val make_while : Rename.t -> local_env
         -> (term * term * pure_type) (* typed variant *)
         -> cc_term * type_c
         -> (cc_term * type_c) block
         -> assertion option * type_c
         -> cc_term

val make_letrec : Rename.t -> local_env
         -> (Ident.t * (term * term * pure_type)) (* typed variant *)
	 -> Ident.t (* the name of the function *)
         -> (cc_binder list)
	 -> (cc_term * type_c)
	 -> type_c
         -> cc_term

