(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
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

(*i $Id: loc.mli,v 1.17 2006-11-03 12:49:03 marche Exp $ i*)

open Format

(*s Line number for an absolute position *)

val report_line : formatter -> Lexing.position -> unit

(* Lexing positions *)

type position = Lexing.position * Lexing.position

exception Located of position * exn

val string : position -> string

val dummy_position : position

val gen_report_position : formatter -> position -> unit
val report_position : formatter -> position -> unit
val report_obligation_position : formatter -> position -> unit

(* for both type [t] and [position] *)

val join : 'a * 'b -> 'a * 'b -> 'a * 'b

val current_offset : int ref
val reloc : Lexing.position -> Lexing.position

(* Identifiers localization *)

val add_ident : string -> position -> unit
val ident : string -> position
