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
