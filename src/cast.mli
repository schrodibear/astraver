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

(*i $Id: cast.mli,v 1.20 2003-12-05 15:49:30 filliatr Exp $ i*)

(* C abstract syntax trees *)

open Logic
open Ptree

type annot = int * string

type storage_class = No_storage | Extern | Auto | Static | Register

type ctype_expr =
  | CTvoid
  | CTchar
  | CTshort
  | CTint
  | CTlong
  | CTfloat
  | CTdouble
  | CTvar of string
  | CTarray of ctype_expr
  | CTpointer of ctype_expr
  (* only for the sym table *)
  | CTfun of ctype list * ctype_expr

and ctype = { 
  ctype_expr : ctype_expr;
  ctype_storage : storage_class;
  ctype_const : bool;
  ctype_volatile : bool;
  ctype_signed : bool 
}

type assign_operator = 
  | Aequal | Amul | Adiv | Amod | Aadd | Asub | Aleft | Aright 
  | Aand | Axor | Aor

type unary_operator = 
  | Prefix_inc | Prefix_dec | Postfix_inc | Postfix_dec 
  | Uplus | Uminus | Not | Ustar | Uamp | Utilde

type binary_operator =
  | Plus | Minus | Mult | Div | Mod | Lt | Gt | Le | Ge | Eq | Neq 
  | Bw_and | Bw_xor | Bw_or | And | Or

type shift = Left | Right

type cexpr =
  | CEnop of Loc.t
  | CEconstant of Loc.t * string
  | CEstring_literal of Loc.t * string
  | CEvar of Loc.t * string
  | CEdot of Loc.t * cexpr * string
  | CEarrow of Loc.t * cexpr * string
  | CEarrget of Loc.t * cexpr * cexpr
  | CEseq of Loc.t * cexpr * cexpr
  | CEassign of Loc.t * cexpr * assign_operator * cexpr
  | CEunary of Loc.t * unary_operator * cexpr
  | CEbinary of Loc.t * cexpr * binary_operator * cexpr
  | CEcall of Loc.t * cexpr * cexpr list
  | CEcond of Loc.t * cexpr * cexpr * cexpr
  | CEshift of Loc.t * cexpr * shift * cexpr
  | CEcast of Loc.t * ctype * cexpr
  | CEsizeof_expr of Loc.t * cexpr
  | CEsizeof of Loc.t * ctype

type c_initializer = 
  | Inothing
  | Iexpr of cexpr
  | Ilist of c_initializer list

type cstatement = 
  | CSnop of Loc.t
  | CSexpr of Loc.t * cexpr
  | CScond of Loc.t * cexpr * cstatement * cstatement
  | CSwhile of Loc.t * cexpr * annot * cstatement
  | CSdowhile of Loc.t * cstatement * annot * cexpr
  | CSfor of Loc.t * cexpr * cexpr * cexpr option * annot * cstatement
  | CSblock of Loc.t * block
  | CSreturn of Loc.t * cexpr option
  | CSbreak of Loc.t
  | CScontinue of Loc.t
  | CSlabel of Loc.t * string * cstatement
  | CSswitch of Loc.t * cexpr * cstatement
  | CScase of Loc.t * cexpr * cstatement
  | CSdefault of Loc.t * cstatement
  | CSgoto of Loc.t * string
  | CSannot of Loc.t * annot

and block = decl list * cstatement list

and annotated_block = Loc.t * annot option * block * annot option

and decl = 
  | Cspecdecl of annot
  | Ctypedef of Loc.t * ctype * string
  | Cdecl of Loc.t * ctype * string * c_initializer
  | Cfundef of Loc.t * ctype * string * parameters * annotated_block

and parameters = (ctype * string) list

type file = decl list


