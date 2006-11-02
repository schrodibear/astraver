(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe Filliâtre
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

(*i $Id: linenum.mli,v 1.3 2006-11-02 09:18:23 hubert Exp $ i*)

(* [from_char f n] gives the actual source file, line number, position of the
   beginning of the line. *)

val from_char : string -> int -> string * int * int
