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

(*i $Id: ctyping.mli,v 1.8 2006-01-26 17:01:55 hubert Exp $ i*)

(* Typing C programs *)
val tezero : Cast.texpr

val type_file : Cast.file -> Cast.tfile

val is_null : Cast.texpr -> bool

val eval_const_expr : Cast.texpr -> int64
val eval_const_expr_noerror : Cast.texpr -> int64

val int_teconstant : string -> Cast.texpr

