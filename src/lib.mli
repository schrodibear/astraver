(*
 * The Why and Caduceus certification tools
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

(*i $Id: lib.mli,v 1.4 2004-10-20 12:56:43 hubert Exp $ i*)

module Sset : Set.S with type elt = string

val mkdir_p : string -> unit

(* [file dir file] returns "dir/basename" if [file] is "dirname/basename", 
   creating [dir] if necessary. *)
val file : dir:string -> file:string -> string

