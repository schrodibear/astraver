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

(* $Id: jc_envset.mli,v 1.10 2007-11-30 09:12:39 moy Exp $ *)

open Jc_env

module StringSet : Set.S with type elt = string

module StringMap : Map.S with type key = string 

val get_unique_name : ?local_names:StringSet.t -> string -> string

module VarSet : Set.S with type elt = var_info

module StructSet : Set.S with type elt = struct_info

module ExceptionSet : Set.S with type elt = exception_info

module ExceptionMap : Map.S with type key = exception_info

module FieldSet : Set.S with type elt = field_info

module FieldMap : Map.S with type key = field_info

(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)

