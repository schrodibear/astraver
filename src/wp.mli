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

(*i $Id: wp.mli,v 1.11 2005-11-03 14:11:37 filliatr Exp $ i*)

(*s Weakest preconditions *)

open Env

val wp : typed_expr -> typed_expr * Ast.assertion option

(**
val wp : typed_expr -> Ast.assertion option * (Cc.proof_term -> typed_expr)
***)
