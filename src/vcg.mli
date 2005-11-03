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

(*s Verification Conditions Generator. *)

open Types
open Logic
open Cc

type context_element =
  | Svar of Ident.t * cc_type
  | Spred of Ident.t * predicate

type sequent = context_element list * predicate

type obligation = Loc.position * string * sequent

type validation = proof cc_term

val vcg : 
  string -> (Loc.position * predicate) cc_term -> obligation list * validation

val logs : Log.t ref
val log_print_function : (Format.formatter -> sequent -> unit) ref

(* obligations from the WP *)

val vcg_from_wp : string -> Ast.assertion -> obligation list * proof

(* functions to be reused in module [Coq] *)

val annotated_if : Ident.t -> cc_binder list -> bool
val annotation_if : cc_binder list -> Ident.t * predicate

