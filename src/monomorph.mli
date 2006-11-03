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

(*i $Id: monomorph.mli,v 1.10 2006-11-03 12:49:04 marche Exp $ i*)

(* make a monorphic output for provers not supporting polymorphism
   (e.g. PVS or CVC Lite) *)

(* input... *)

val push_decl : Logic_decl.t -> unit

val add_external : Ident.t -> unit

(* ...and output *)

val iter : (Logic_decl.t -> unit) -> unit

val reset : unit -> unit

(* [symbol id i] prints the instance [i] of symbol [id] using the same 
   conventions as in the monomorphization process *)

val symbol : Ident.t * Logic.instance -> string
