(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filliâtre - Claude Marché
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

(*i $Id: ctyping.mli,v 1.6 2004-12-07 17:19:24 hubert Exp $ i*)

(* Typing C programs *)

val type_file : Cast.file -> Cast.tfile

val is_null : Cast.texpr -> bool

val eval_const_expr : Cast.texpr -> int64

val int_teconstant : string -> Cast.texpr

