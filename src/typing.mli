(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: typing.mli,v 1.6 2002-03-11 16:22:38 filliatr Exp $ i*)

open Logic
open Types
open Ast
open Env

(* This module realizes type and effect inference *)

module LabelSet : Set.S with type elt = string

val initial_labels : LabelSet.t

val check_type_v : Loc.t option -> LabelSet.t -> local_env -> type_v -> unit

val effect_app : Rename.t -> local_env
            -> typing_info Ast.t
            -> typing_info arg list
            -> (type_v binder list * type_c) 
             * ((Ident.t * Ident.t) list * (Ident.t * term) list * bool)
             * type_c

val typed_var : local_env -> term * term -> variant

val typef : LabelSet.t -> local_env -> parsed_program -> typed_program

