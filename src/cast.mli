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

(*i $Id: cast.mli,v 1.6 2002-11-07 12:20:17 filliatr Exp $ i*)

(* C abstract syntax trees *)

open Logic
open Ptree

type constant_expression = unit

type annot = int * string

type parameters = (pure_type * Ident.t) list

type declarator =
  | CDvar of Ident.t
  | CDarr of Ident.t * constant_expression
  | CDfun of Ident.t * parameters * annot option

type assign_operator = 
  | Aequal | Amul | Adiv | Amod | Aadd | Asub | Aleft | Aright 
  | Aand | Axor | Aor

type lvalue = 
  | Lvar of Loc.t * Ident.t

type cexpr =
  | CEvar of Loc.t * Ident.t
  | CEseq of Loc.t * cexpr * cexpr
  | CEassign of Loc.t * lvalue * assign_operator * cexpr

type cstatement = 
  | CSexpr of Loc.t * cexpr

type block = Loc.t * annot option * cstatement list * annot option

type decl = 
  | Ctypedecl of Loc.t * declarator * pure_type
  | Cfundef of Loc.t * Ident.t * parameters * pure_type * block

type file = decl list
