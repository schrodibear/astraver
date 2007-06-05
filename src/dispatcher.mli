(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
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

(*i $Id: dispatcher.mli,v 1.16 2007-06-05 11:29:14 couchot Exp $ i*)

open Cc

val push_decl : Logic_decl.t -> unit

val iter : (Loc.position * string * sequent Env.scheme -> unit) -> unit

type prover = Simplify | Harvey | Cvcl | Zenon | Rvsat | Yices | Ergo | Cvc3 | Graph

val call_prover : 
  ?debug:bool -> ?timeout:int -> ?encoding:Options.encoding ->
  obligation:string -> prover -> Calldp.prover_result
