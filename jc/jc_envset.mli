(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2007                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
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

(* $Id: jc_envset.mli,v 1.12 2007-12-17 13:18:48 moy Exp $ *)

open Jc_env

module StringSet : Set.S with type elt = string

module StringMap : Map.S with type key = string 

val get_unique_name : ?local_names:StringSet.t -> string -> string

val is_pointer_type : Jc_env.jc_type -> bool

module VarSet : Set.S with type elt = var_info

module StructSet : Set.S with type elt = struct_info

module ExceptionSet : Set.S with type elt = exception_info

module ExceptionMap : Map.S with type key = exception_info

module FieldOrd : Set.OrderedType with type t = field_info

module FieldSet : Set.S with type elt = field_info

module FieldMap : Map.S with type key = field_info

module FieldTable : Hashtbl.S with type key = field_info

(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)

