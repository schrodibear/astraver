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

(*i $Id: creport.mli,v 1.17 2007-11-20 14:34:49 filliatr Exp $ i*)

open Format

exception Error of (Loc.position option) * Cerror.t

val report : formatter -> Cerror.t -> unit

val raise_located : Loc.position -> Cerror.t -> 'a 
val raise_unlocated : Cerror.t -> 'a
val raise_locop : Loc.position option -> Cerror.t -> 'a
val unsupported : Loc.position -> string -> 'a

val print_type : formatter -> Ctypes.ctype -> unit
val print_type_node : formatter -> Ctypes.ctype_node -> unit

val error : Loc.position -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val warning : Loc.position -> ('a, Format.formatter, unit, unit) format4 -> 'a


