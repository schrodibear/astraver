(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2007                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Xavier URBAIN                                                       *)
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

(*i $Id: pp.mli,v 1.12 2008-01-24 14:08:24 moy Exp $ i*)

open Format

val print_option : (formatter -> 'a -> unit) -> formatter -> 'a option -> unit
val print_option_or_default :
  string -> (formatter -> 'a -> unit) -> formatter -> 'a option -> unit
val print_list : 
  (formatter -> unit -> unit) -> 
  (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
val print_list_or_default :
  string -> (formatter -> unit -> unit) -> 
  (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
val print_list_par :
  (Format.formatter -> unit -> 'a) ->
  (Format.formatter -> 'b -> unit) -> Format.formatter -> 'b list -> unit
val space : formatter -> unit -> unit
val alt : formatter -> unit -> unit
val newline : formatter -> unit -> unit
val comma : formatter -> unit -> unit
val semi : formatter -> unit -> unit
val underscore : formatter -> unit -> unit
val arrow : formatter -> unit -> unit
val nothing : formatter -> unit -> unit
val hov : int -> formatter -> ('a -> unit) -> 'a -> unit

val open_formatter : ?margin:int -> out_channel -> formatter
val close_formatter : formatter -> unit
val open_file_and_formatter : ?margin:int -> string -> out_channel * formatter
val close_file_and_formatter : out_channel * formatter -> unit
val print_in_file_no_close : ?margin:int -> (Format.formatter -> unit) -> string -> out_channel
val print_in_file : ?margin:int -> (Format.formatter -> unit) -> string -> unit
