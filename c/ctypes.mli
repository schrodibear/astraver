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

(*i $Id: ctypes.mli,v 1.9 2005-06-09 08:31:22 filliatr Exp $ i*)

(* Parsing C requires to separate identifiers and type names during
   lexical analysis. This table is for this purpose. It is fill during
   syntactic analysis. *)


type storage_class = No_storage | Extern | Auto | Static | Register

type sign = Signed | Unsigned

type cinteger = Char | Short | Int | Long | LongLong | Bitfield of int64

type cfloat = Float | Double | LongDouble

type ctype_node =
  | Tvoid
  | Tint of sign * cinteger
  | Tfloat of cfloat
  | Tvar of string
  | Tarray of ctype * int64 option 
  | Tpointer of ctype
  | Tstruct of string 
  | Tunion of string 
  | Tenum of string 
  | Tfun of ctype list * ctype

and ctype = { 
  ctype_node : ctype_node;
  ctype_storage : storage_class;
  ctype_const : bool;
  ctype_volatile : bool;
  ctype_ghost : bool;
}


val noattr : ctype_node -> ctype
val c_void : ctype
val c_int : ctype
val c_float : ctype
val c_string : ctype
val c_array :  ctype ->  ctype
val c_array_size :  ctype -> int64 ->  ctype
val c_pointer :  ctype ->  ctype
val c_void_star : ctype
val c_addr : ctype

val add : string -> unit

val remove : string -> unit

val mem : string -> bool

val push : unit -> unit

val pop : unit -> unit

val ctype : Format.formatter -> ctype -> unit

