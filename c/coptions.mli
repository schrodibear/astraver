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

(*i $Id: coptions.mli,v 1.4 2004-01-30 16:58:37 marche Exp $ i*)

val parse_only : bool
val type_only : bool
val debug : bool
val verbose : bool
val werror : bool
val with_cpp : bool
val cpp_command : string

val files : string Queue.t

(*s The log file *)

val log : Format.formatter;;
val close_log : unit -> unit;;

