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

(*i $Id: creport.mli,v 1.9 2005-03-23 14:59:18 filliatr Exp $ i*)

open Format

exception Error of (Loc.t option) * Cerror.t

val report : formatter -> Cerror.t -> unit

val raise_located : Loc.t -> Cerror.t -> 'a 
val raise_unlocated : Cerror.t -> 'a
val raise_locop : Loc.t option -> Cerror.t -> 'a
val unsupported : Loc.t -> string -> 'a

val print_type : formatter -> Ctypes.ctype -> unit
val print_type_node : formatter -> Ctypes.ctype_node -> unit

val error : Loc.t -> string -> 'a
val warning : Loc.t -> string -> unit

val reloc : Loc.t -> Loc.t
val with_offset : int -> ('a -> 'b) -> 'a -> 'b

