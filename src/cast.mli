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

(*i $Id: cast.mli,v 1.4 2002-10-17 15:01:52 filliatr Exp $ i*)

(* C abstract syntax trees *)

open Logic
open Ptree

type constant_expression = unit

type annot = string

type declarator =
  | CDvar of Ident.t
  | CDarr of Ident.t * constant_expression
  | CDfun of Ident.t * (pure_type * Ident.t) list * annot option

type decl = 
  | Ctypedecl of Loc.t * declarator * pure_type

type file = decl list
