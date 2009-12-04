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
(*  License version 2, with the special exception on linking              *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)



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


