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

(*i $Id: cast.mli,v 1.6 2003-12-23 13:23:41 filliatr Exp $ i*)

(*s C types *)

type storage_class = No_storage | Extern | Auto | Static | Register

type sign = Signed | Unsigned

type cinteger = Char | Short | Int | Long | LongLong

type cfloat = Float | Double | LongDouble

type 'expr ctype_node =
  | CTvoid
  | CTint of sign * cinteger
  | CTfloat of cfloat
  | CTvar of string
  | CTarray of 'expr ctype_node * 'expr option
  | CTpointer of 'expr ctype_node
  | CTbitfield of 'expr ctype_node * 'expr
  | CTstruct_named of string
  | CTstruct_decl of string option * 'expr parameters 
  | CTunion_named of string
  | CTunion_decl of string option * 'expr parameters
  | CTenum_named of string
  | CTenum_decl of string option * (string * 'expr option) list
  | CTfun of 'expr parameters * 'expr ctype_node

and 'expr ctype = { 
  ctype_node : 'expr ctype_node;
  ctype_storage : storage_class;
  ctype_const : bool;
  ctype_volatile : bool;
}

and 'expr parameters = ('expr ctype * string) list

(*s C parsed abstract syntax trees *)

type 'a located = { node : 'a; loc : Loc.t }

type annot = int * string

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

type cexpr = cexpr_node located

and cexpr_node =
  | CEnop
  | CEconstant of string
  | CEstring_literal of string
  | CEvar of string
  | CEdot of cexpr * string
  | CEarrow of cexpr * string
  | CEarrget of cexpr * cexpr
  | CEseq of cexpr * cexpr
  | CEassign of cexpr * assign_operator * cexpr
  | CEunary of unary_operator * cexpr
  | CEbinary of cexpr * binary_operator * cexpr
  | CEcall of cexpr * cexpr list
  | CEcond of cexpr * cexpr * cexpr
  | CEshift of cexpr * shift * cexpr
  | CEcast of cexpr ctype * cexpr
  | CEsizeof_expr of cexpr
  | CEsizeof of cexpr ctype

type c_initializer = 
  | Inothing
  | Iexpr of cexpr
  | Ilist of c_initializer list

type cstatement = cstatement_node located

and cstatement_node =
  | CSnop
  | CSexpr of cexpr
  | CScond of cexpr * cstatement * cstatement
  | CSwhile of cexpr * annot * cstatement
  | CSdowhile of cstatement * annot * cexpr
  | CSfor of cexpr * cexpr * cexpr option * annot * cstatement
  | CSblock of block
  | CSreturn of cexpr option
  | CSbreak
  | CScontinue
  | CSlabel of string * cstatement
  | CSswitch of cexpr * cstatement
  | CScase of cexpr * cstatement
  | CSdefault of cstatement
  | CSgoto of string
  | CSannot of annot

and block = decl located list * cstatement list

and annotated_block = annot option * block * annot option

and decl = 
  | Cspecdecl of annot
  | Ctypedef of cexpr ctype * string
  | Ctypedecl of cexpr ctype
  | Cdecl of cexpr ctype * string * c_initializer
  | Cfundef of 
      cexpr ctype * string * cexpr parameters * annotated_block located

type file = decl located list


