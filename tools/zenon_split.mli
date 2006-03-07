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

(*i $Id: zenon_split.mli,v 1.1 2006-03-07 15:12:01 filliatr Exp $ i*)

(* Split a Zenon input file into several files, one for each query.
   The function passed is iterated over each sub-file. *)

val iter : (string -> unit) -> string -> unit

val debug : bool ref
