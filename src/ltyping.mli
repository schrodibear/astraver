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

(*i $Id: ltyping.mli,v 1.12 2003-12-18 12:24:06 marche Exp $ i*)

(*s Typing on the logical side *)

open Logic
open Types
open Ptree
open Ast
open Env

val unify : Logic.pure_type -> Logic.pure_type -> bool

val type_v : 
  Loc.t -> Label.t -> local_env -> logical_env -> ptype_v -> type_v

val type_c :
  Loc.t -> Label.t -> local_env -> logical_env -> ptype_c -> type_c

val predicate : 
  Label.t -> local_env -> logical_env -> lexpr -> predicate

val term : 
  Label.t -> local_env -> logical_env -> lexpr -> term * pure_type

val type_assert : 
  Label.t -> local_env -> logical_env -> lexpr asst -> assertion

val type_post : 
  Label.t -> local_env -> logical_env -> Ident.t -> type_v -> Effect.t -> 
  lexpr post -> postcondition

val binders : 
  Loc.t -> Label.t -> local_env -> logical_env -> 
  ptype_v binder list -> 
  type_v binder list * local_env * logical_env

(* errors *)

val expected_num : Loc.t -> 'a
