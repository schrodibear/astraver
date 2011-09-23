(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)



(*s Typing on the logical side *)

open Logic
open Types
open Ptree
open Ast
open Env

val unify : Logic.pure_type -> Logic.pure_type -> bool

val pure_type : local_env -> ppure_type -> pure_type

val type_v : 
  Loc.position -> Label.t -> local_env -> ptype_v -> type_v

val type_c :
  Loc.position -> Label.t -> local_env -> ptype_c -> type_c

val logic_type : plogic_type -> logic_type

val alg_type : Ident.t -> Ident.t list ->
  (Loc.position * Ident.t * ppure_type list) list ->
    alg_type_def

val predicate : Label.t -> local_env -> lexpr -> predicate

val term : Label.t -> local_env -> lexpr -> term * pure_type

val type_assert : 
  ?namer:(Ident.name -> Ident.t) ->
  Label.t -> local_env -> Ptree.assertion -> assertion

val type_post : 
  Label.t -> local_env -> Ident.t -> type_v -> Effect.t -> 
  Ptree.postcondition -> postcondition

val binders : 
  Loc.position -> Label.t -> local_env -> 
  ptype_v binder list -> 
  type_v binder list * local_env

val instance : Ident.t -> var_subst -> pure_type list

(* errors *)

val expected_real : Loc.position -> 'a

val expected_num : Loc.position -> 'a

val expected_type : Loc.position -> type_v -> 'a

(* instances: the following table contains all closed instances of logical
   symbols that have been used so far. 
   It is later used to generate all monomorphic
   instances of symbols/predicates/axioms in the CVC Lite output. *)
(*
module Instances : Set.S with type elt = pure_type list

val add_instance_if_closed : Ident.t -> pure_type list -> unit
val instances : Ident.t -> Instances.t

val iter_instances : (Ident.t -> pure_type list -> unit) -> unit
*)
