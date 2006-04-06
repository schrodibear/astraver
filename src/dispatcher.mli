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

(*i $Id: dispatcher.mli,v 1.7 2006-04-06 14:26:44 filliatr Exp $ i*)

open Cc

val push_decl : Logic_decl.t -> unit

val iter : (Loc.position * string * sequent Env.scheme -> unit) -> unit

type prover = Simplify | Harvey | Cvcl | Zenon

val call_prover : 
  obligation:string -> ?timeout:int -> prover -> Calldp.prover_result
