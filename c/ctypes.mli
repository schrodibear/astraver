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

(*i $Id: ctypes.mli,v 1.4 2003-12-23 09:18:57 filliatr Exp $ i*)

(* Parsing C requires to separate identifiers and type names during
   lexical analysis. This table is for this purpose. It is fill during
   syntactic analysis. *)

val add : string -> unit

val remove : string -> unit

val mem : string -> bool

val push : unit -> unit

val pop : unit -> unit

