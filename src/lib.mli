(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
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

(*i $Id: lib.mli,v 1.8 2006-11-03 12:49:03 marche Exp $ i*)

module Sset : Set.S with type elt = string

val mkdir_p : string -> unit

(* [file dir file] returns "dir/basename" if [file] is "dirname/basename", 
   creating [dir] if necessary. *)
val file : dir:string -> file:string -> string

(* [file_copy_if_different f1 f2] copies [f1] into name [f2], unless
   [f2] already exists and is identical to [f1] (thus keeping the same
   modification date) *)
val file_copy_if_different : string -> string -> unit


