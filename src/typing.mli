(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: typing.mli,v 1.4 2002-02-28 16:15:13 filliatr Exp $ i*)

open Logic
open Types
open Ast
open Env

(* This module realizes type and effect inference *)

module LabelSet : Set.S with type elt = string

val initial_labels : LabelSet.t

(*i val cic_type_v : local_env -> Rename.t -> type_v -> type_v i*)

val effect_app : Rename.t -> local_env
            -> typing_info Ast.t
            -> typing_info arg list
            -> (type_v binder list * type_c) 
             * ((Ident.t * Ident.t) list * (Ident.t * term) list * bool)
             * type_c

val typed_var : local_env -> term * term -> variant

val typef : LabelSet.t -> local_env -> parsed_program -> typed_program

val type_of_expression : LabelSet.t -> local_env -> term -> type_v
