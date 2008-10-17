(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann R�GIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: ctypes.mli,v 1.23 2008-10-17 11:49:29 filliatr Exp $ i*)

(* Parsing C requires to separate identifiers and type names during
   lexical analysis. This table is for this purpose. It is fill during
   syntactic analysis. *)


type storage_class = No_storage | Extern | Auto | Static | Register

type sign = Signed | Unsigned

type cinteger = 
  | Char | Short | Int | Long | LongLong | Bitfield of int64
  | ExactInt

type cfloat = Float | Double | LongDouble | Real

type valid = Valid of int64 * int64 | Not_valid 

type ctype_node =
  | Tvoid
  | Tint of (sign * cinteger)
  | Tfloat of cfloat
  | Tvar of string
  | Tarray of valid * ctype * int64 option 
  | Tpointer of valid * ctype
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
val c_exact_int : ctype
val c_float : cfloat -> ctype
val c_string : valid -> ctype
val c_array :  valid -> ctype ->  ctype
val c_array_size : valid ->  ctype -> int64 ->  ctype
val c_pointer :  valid -> ctype ->  ctype
val c_void_star : valid -> ctype
val c_real : ctype
val c_addr : ctype

val add : string -> unit

val remove : string -> unit

val mem : string -> bool

val push : unit -> unit

val pop : unit -> unit

val ctype : Format.formatter -> ctype -> unit

val is_pointer : ctype -> bool


val float_constant_type : in_logic:bool -> string -> string * cfloat
