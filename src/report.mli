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

(*i $Id: report.mli,v 1.3 2004-07-19 15:35:20 filliatr Exp $ i*)

open Format

exception Error of (Loc.t option) * Error.t

val report : formatter -> Error.t -> unit

val raise_located : Loc.t -> Error.t -> 'a 
val raise_unlocated : Error.t -> 'a
val raise_locop : Loc.t option -> Error.t -> 'a

val explain_exception : formatter -> exn -> unit
