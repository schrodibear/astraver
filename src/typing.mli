
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: typing.mli,v 1.1 2001-08-17 00:52:39 filliatr Exp $ *)

open Logic
open Types
open Ast
open Env

(* This module realizes type and effect inference *)

val cic_type_v : local_env -> Rename.t -> type_v -> type_v

val effect_app : Rename.t -> local_env
            -> typing_info Ast.t
            -> typing_info arg list
            -> (type_v binder list * type_c) 
             * ((Ident.t * Ident.t) list * (Ident.t * term) list * bool)
             * type_c

val typed_var : Rename.t -> local_env -> term * term -> variant

val states : Rename.t -> local_env -> parsed_program -> typed_program

val type_of_expression : Rename.t -> local_env -> term -> type_v
