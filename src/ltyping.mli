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

(*i $Id: ltyping.mli,v 1.7 2002-10-17 15:01:53 filliatr Exp $ i*)

(*s Typing on the logical side *)

open Logic
open Types
open Ptree
open Ast
open Env

val type_v : 
  Loc.t -> LabelSet.t -> local_env -> logical_env -> ptype_v -> type_v

val type_c :
  Loc.t -> LabelSet.t -> local_env -> logical_env -> ptype_c -> type_c

val predicate : 
  LabelSet.t -> logical_env -> lexpr -> predicate

val term : 
  LabelSet.t -> logical_env -> lexpr -> term * pure_type

val type_pre : LabelSet.t -> logical_env -> lexpr pre -> precondition
val type_assert : LabelSet.t -> logical_env -> lexpr asst -> assertion
val type_post : 
  LabelSet.t -> logical_env -> Ident.t -> type_v -> lexpr post -> postcondition

val binders : 
  Loc.t -> LabelSet.t -> local_env -> logical_env -> 
  ptype_v binder list -> 
  type_v binder list * local_env * logical_env

(* errors *)

val expected_num : Loc.t -> 'a
