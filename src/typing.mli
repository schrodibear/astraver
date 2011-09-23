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



(*s This module realizes type and effect inference *)

open Types
open Ptree
open Ast
open Env

val typef : Label.t -> local_env -> parsed_program -> typed_expr

val check_for_not_mutable : Loc.position -> type_v -> unit

val is_pure_type : type_v -> bool
val is_pure_type_v : type_v -> bool

val type_c_of_typing_info : assertion list -> typing_info -> type_c
val typing_info_of_type_c : 
  Loc.position -> local_env -> label -> type_c -> typing_info

(*
val gmake_node : 
  Loc.position ->
    local_env ->
    label -> (* userlabel *)
    label ->
    ?post:postcondition option ->
    typing_info t_desc ->
    type_v -> Effect.t -> typed_expr
*)

val conj : postcondition option -> postcondition option -> postcondition option


