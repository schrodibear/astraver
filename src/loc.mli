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

(*i $Id: loc.mli,v 1.11 2005-11-03 14:11:36 filliatr Exp $ i*)

open Format

(*s Error location. *)

type t = int * int

val dummy : t

val set_file : string -> unit
val get_file : unit -> string (* for C's __FILE__ *)

(*s Line number for an absolute position *)

val line : int -> int

val report_line : formatter -> int -> unit

(*s Error reporting. *)

val string : t -> string

val report : formatter -> t -> unit
val report_obligation : formatter -> t -> unit

(* Lexing positions *)

type position = Lexing.position * Lexing.position

val dummy_position : position

val report_position : formatter -> position -> unit
val report_obligation_position : formatter -> position -> unit

(* for both type [t] and [position] *)

val join : 'a * 'b -> 'a * 'b -> 'a * 'b

