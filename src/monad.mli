(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: monad.mli,v 1.8 2002-03-13 14:26:41 filliatr Exp $ i*)

(*s Main part of the translation of imperative programs into functional ones
   (with module [Mlize]) *)

open Logic
open Types
open Ast
open Env

(*s Translation of types *)

val trad_ml_type_v : Rename.t -> local_env -> type_v -> cc_type
val trad_ml_type_c : Rename.t -> local_env -> type_c -> cc_type
val trad_imp_type  : Rename.t -> local_env -> type_v -> cc_type
val trad_type_in_env : Rename.t -> local_env -> Ident.t -> cc_type

(*s Monadic operators *)

type interp = Rename.t -> cc_term

val unit : typing_info -> term -> interp

val compose : typing_info -> interp ->
              (Ident.t -> interp) ->
	      interp

val cross_label : string -> interp -> interp

val insert_pre : local_env -> precondition -> interp -> interp

val insert_many_pre : local_env -> precondition list -> interp -> interp

val abstraction : local_env -> type_c -> interp -> interp

val fresh : Ident.t -> (Ident.t -> interp) -> interp

(*i******

(*s The following functions translate the main constructions *)

val result_tuple : Rename.t -> string -> local_env
          -> (Ident.t * cc_term * cc_type) -> (Effect.t * postcondition option)
          -> cc_term * cc_type

val let_in_pre : cc_type -> precondition -> cc_term -> cc_term

val make_let_in : Rename.t -> Rename.t -> local_env -> cc_term 
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

*****i*)
