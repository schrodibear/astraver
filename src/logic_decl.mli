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

(*i $Id: logic_decl.mli,v 1.2 2006-04-06 14:26:44 filliatr Exp $ i*)

(*s Logical declarations. 
    This is what is sent to the various provers (see main.ml and the provers
    interfaces). *)

open Cc
open Logic

type loc = Loc.position
type 'a scheme = 'a Env.scheme

type t = 
  | Dtype of loc * string list * string
  | Dlogic of loc * string * logic_type scheme
  | Dpredicate_def of loc * string * predicate_def scheme
  | Dfunction_def of loc * string * function_def scheme
  | Daxiom of loc * string * predicate scheme
  | Dgoal of loc * string * sequent scheme

