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

(*i $Id: cast.mli,v 1.10 2002-11-26 16:54:21 filliatr Exp $ i*)

(* C abstract syntax trees *)

open Logic
open Ptree

type constant_expression = unit

type annot = int * string

type parameters = (pure_type * Ident.t) list

type assign_operator = 
  | Aequal | Amul | Adiv | Amod | Aadd | Asub | Aleft | Aright 
  | Aand | Axor | Aor

type unary_operator = 
  | Prefix_inc | Prefix_dec | Postfix_inc | Postfix_dec | Uplus | Uminus | Not

type binary_operator =
  | Plus | Minus | Mult | Div | Mod | Lt | Gt | Le | Ge | Eq | Neq 
  | Bw_and | Bw_xor | Bw_or | And | Or

type cexpr =
  | CEnop of Loc.t
  | CEconst of Loc.t * string
  | CEvar of Loc.t * Ident.t
  | CEarrget of Loc.t * cexpr * cexpr
  | CEseq of Loc.t * cexpr * cexpr
  | CEassign of Loc.t * cexpr * assign_operator * cexpr
  | CEunary of Loc.t * unary_operator * cexpr
  | CEbinary of Loc.t * cexpr * binary_operator * cexpr
  | CEcall of Loc.t * cexpr * cexpr list
  | CEcond of Loc.t * cexpr * cexpr * cexpr

type c_initializer = cexpr option

type declarator =
  | CDvar of Ident.t * c_initializer
  | CDarr of Ident.t * constant_expression
  | CDfun of Ident.t * parameters * annot option

type cstatement = 
  | CSnop of Loc.t
  | CSexpr of Loc.t * cexpr
  | CScond of Loc.t * cexpr * cstatement * cstatement
  | CSwhile of Loc.t * cexpr * annot * cstatement
  | CSdowhile of Loc.t * cstatement * annot * cexpr
  | CSfor of Loc.t * cexpr * cexpr * cexpr option * annot * cstatement
  | CSblock of Loc.t * block
  | CSreturn of Loc.t * cexpr option

and block = decl list * cstatement list

and annotated_block = Loc.t * annot option * block * annot option

and decl = 
  | Ctypedecl of Loc.t * declarator * pure_type
  | Cfundef of Loc.t * Ident.t * parameters * pure_type * annotated_block

type file = decl list
