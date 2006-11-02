(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
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

(*i $Id: zenon.mli,v 1.4 2006-11-02 09:18:26 hubert Exp $ i*)

open Cc

val reset : unit -> unit

val push_decl : Logic_decl.t -> unit

val prelude_done : bool ref
val output_file : string -> unit

