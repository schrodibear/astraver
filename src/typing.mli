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

(*i $Id: typing.mli,v 1.11 2002-10-17 15:01:54 filliatr Exp $ i*)

(*s This module realizes type and effect inference *)

open Logic
open Types
open Ptree
open Ast
open Env

val typef : LabelSet.t -> local_env -> parsed_program -> typed_program

val check_for_not_mutable : Loc.t -> type_v -> unit

