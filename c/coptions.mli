(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filliâtre - Claude Marché
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

(*i $Id: coptions.mli,v 1.10 2004-11-08 16:10:01 filliatr Exp $ i*)

(*s environment variables *)

val libdir : string

(*s command-line options *)

val parse_only : bool
val type_only : bool
val debug : bool
val verbose : bool
val werror : bool
val with_cpp : bool
val cpp_command : string
val cpp_dump : bool
val why_opt : string
val coq_tactic : string
val separate : bool

val files : unit -> string list 

val verify : string -> bool

(*s The log file *)

val log : Format.formatter;;
val lprintf : ('a, Format.formatter, unit) format -> 'a
val close_log : unit -> unit;;

