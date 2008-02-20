(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann RÉGIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
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

(*i $Id: dispatcher.mli,v 1.24 2008-02-20 14:34:26 marche Exp $ i*)

open Cc

val push_decl : Logic_decl.t -> unit

val iter : 
    (Loc.floc * Logic_decl.vc_expl * string * sequent Env.scheme -> unit) 
    -> unit

type prover = 
  | Simplify | Harvey | Cvcl | Zenon | Rvsat | Yices | Ergo 
  | Cvc3 | Graph | Z3

val call_prover : 
  ?debug:bool -> ?timeout:int -> ?encoding:Options.encoding ->
  obligation:string -> prover -> Calldp.prover_result
