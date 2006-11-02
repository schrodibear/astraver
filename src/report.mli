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

(*i $Id: report.mli,v 1.6 2006-11-02 09:18:25 hubert Exp $ i*)

open Format

exception Error of Error.t

val report : formatter -> Error.t -> unit

val raise_located : Loc.position -> Error.t -> 'a 
val raise_unlocated : Error.t -> 'a
val raise_locop : Loc.position option -> Error.t -> 'a

val explain_exception : Format.formatter -> exn -> unit
