(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

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

(*i $Id: typing.mli,v 1.17 2006-11-03 11:55:32 marche Exp $ i*)

(*s This module realizes type and effect inference *)

open Types
open Ptree
open Ast
open Env

val typef : Label.t -> local_env -> parsed_program -> typed_expr

val check_for_not_mutable : Loc.position -> type_v -> unit

val is_pure_type_v : type_v -> bool

val type_c_of_typing_info : assertion list -> typing_info -> type_c
val typing_info_of_type_c : 
  Loc.position -> local_env -> label -> type_c -> typing_info

val gmake_node : 
  Loc.position ->
    local_env ->
    label ->
    ?post:postcondition option ->
    typing_info t_desc ->
    type_v -> Effect.t -> typed_expr

val conj : postcondition option -> postcondition option -> postcondition option


