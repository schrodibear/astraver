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

(*i $Id: cinterp.mli,v 1.10 2006-06-26 14:30:21 filliatr Exp $ i*)

(* Interpretation of C programs *)

open Output

val interp : Cast.nfile -> 
  (string * why_decl) list * why_decl list * prover_decl list

val make_int_ops_decls : unit -> why_decl list
