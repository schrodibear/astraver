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

(*i $Id: loc.mli,v 1.5 2002-10-17 15:01:53 filliatr Exp $ i*)

(*s Error location. *)

type t = int * int

val dummy : t

val join : t -> t -> t

val set_file : string -> unit

(*s Error reporting. *)

open Format

val report : formatter -> t -> unit
