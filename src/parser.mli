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

(*i $Id: parser.mli,v 1.16 2003-12-08 13:03:34 filliatr Exp $ i*)

(* Grammar for the programs *)

open Types
open Ptree

val program : parsed_program Grammar.Entry.e
val type_v  : ptype_v Grammar.Entry.e
val type_c  : ptype_c Grammar.Entry.e

val decls : (decl list) Grammar.Entry.e

