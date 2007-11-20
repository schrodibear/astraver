(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2007                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Xavier URBAIN                                                       *)
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

(*i $Id: logic_decl.mli,v 1.9 2007-11-20 14:34:52 filliatr Exp $ i*)

(*s Logical declarations. 
    This is what is sent to the various provers (see main.ml and the provers
    interfaces). *)

open Cc
open Logic

type loc = Loc.position
type 'a scheme = 'a Env.scheme

type t =
  | Dtype          of loc * string list * string
  | Dlogic         of loc * string * logic_type scheme
  | Dpredicate_def of loc * string * predicate_def scheme
  | Dfunction_def  of loc * string * function_def scheme
  | Daxiom         of loc * string * predicate scheme
  | Dgoal          of loc * vc_explain * string * sequent scheme

