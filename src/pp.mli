(*
 * The Why and Caduceus certification tools
 * Copyright (C) 2003 Jean-Christophe Filli�tre - Claude March�
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

(*i $Id: pp.mli,v 1.4 2004-08-26 13:00:44 filliatr Exp $ i*)

open Format

val print_option : (formatter -> 'a -> unit) -> formatter -> 'a option -> unit
val print_list : 
  (formatter -> unit -> unit) -> 
  (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
val space : formatter -> unit -> unit
val alt : formatter -> unit -> unit
val newline : formatter -> unit -> unit
val comma : formatter -> unit -> unit
val semi : formatter -> unit -> unit
val underscore : formatter -> unit -> unit
val arrow : formatter -> unit -> unit
val nothing : formatter -> unit -> unit
val hov : int -> formatter -> ('a -> unit) -> 'a -> unit

val print_in_file : ?margin:int -> (Format.formatter -> unit) -> string -> unit
