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

(*i $Id: pvs.mli,v 1.9 2002-10-17 15:01:54 filliatr Exp $ i*)

open Format
open Vcg

val reset : unit -> unit

val push_verbatim : string -> unit

val push_obligations : obligation list -> unit

val push_parameter : string -> Cc.cc_type -> unit

val output_file : string -> unit
