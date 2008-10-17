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

(*i $Id: ctyping.mli,v 1.19 2008-10-17 11:49:29 filliatr Exp $ i*)

(* Typing C programs *)
val tezero : Cast.texpr

val type_file : Cast.file -> Cast.tfile

val is_null : Cast.texpr -> bool

val eval_const_expr : Cast.texpr -> int64
val eval_const_expr_noerror : Cast.texpr -> int64

val int_teconstant : string -> Cast.texpr

(*
val float_constant_type : string -> string * Ctypes.cfloat
*)

val coerce : Ctypes.ctype -> Cast.texpr -> Cast.texpr
