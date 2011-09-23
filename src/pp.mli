(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)



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
val print_list_delim :
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> 'b -> unit) -> Format.formatter -> 'b list -> unit

val print_iter1 : 
  (('a -> unit) -> 'b -> unit) ->
  (Format.formatter -> unit -> unit) -> 
  (Format.formatter -> 'a -> unit) -> 
  Format.formatter -> 'b -> unit

val print_iter2: 
  (('a -> 'b -> unit) -> 'c -> unit) ->
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> 'a -> unit) -> 
  (Format.formatter -> 'b -> unit) -> 
  Format.formatter -> 'c -> unit

val print_pair_delim :
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> 'a -> unit) -> 
  (Format.formatter -> 'b -> unit) -> Format.formatter -> 'a * 'b -> unit

val print_pair :
  (Format.formatter -> 'a -> unit) -> 
  (Format.formatter -> 'b -> unit) -> Format.formatter -> 'a * 'b -> unit

val space : formatter -> unit -> unit
val alt : formatter -> unit -> unit
val newline : formatter -> unit -> unit
val comma : formatter -> unit -> unit
val simple_comma : formatter -> unit -> unit
val semi : formatter -> unit -> unit
val underscore : formatter -> unit -> unit
val arrow : formatter -> unit -> unit
val lbrace : formatter -> unit -> unit
val rbrace : formatter -> unit -> unit
val lsquare : formatter -> unit -> unit
val rsquare : formatter -> unit -> unit
val lparen : formatter -> unit -> unit
val rparen : formatter -> unit -> unit
val lchevron : formatter -> unit -> unit
val rchevron : formatter -> unit -> unit
val nothing : formatter -> 'a -> unit
val string : formatter -> string -> unit
val int : formatter -> int -> unit
val constant_string : string -> formatter -> unit -> unit
val hov : int -> formatter -> ('a -> unit) -> 'a -> unit

val open_formatter : ?margin:int -> out_channel -> formatter
val close_formatter : formatter -> unit
val open_file_and_formatter : ?margin:int -> string -> out_channel * formatter
val close_file_and_formatter : out_channel * formatter -> unit
val print_in_file_no_close : ?margin:int -> (Format.formatter -> unit) -> string -> out_channel
val print_in_file : ?margin:int -> (Format.formatter -> unit) -> string -> unit
