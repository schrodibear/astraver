(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: ptyping.mli,v 1.1 2001-08-15 21:08:54 filliatr Exp $ *)

open Names
open Term

open Types
open Ast
open Env

(* This module realizes type and effect inference *)

val cic_type_v : local_env -> Rename.t -> Coqast.t ml_type_v -> type_v

val effect_app : Rename.t -> local_env
            -> (typing_info,'b) Ast.t
            -> (typing_info,constr) arg list
            -> (type_v binder list * type_c) 
             * ((Ident.t*Ident.t) list * (Ident.t*constr) list * bool)
             * type_c

val typed_var : Rename.t -> local_env -> constr * constr -> variant

val type_of_expression : Rename.t -> local_env -> constr -> constr

val states : Rename.t -> local_env -> program -> typed_program
