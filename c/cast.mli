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

(*i $Id: cast.mli,v 1.10 2003-12-24 12:13:35 filliatr Exp $ i*)

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
  | CTarray of 'expr ctype * 'expr option
  | CTpointer of 'expr ctype
  | CTstruct_named of string
  | CTstruct_decl of string option * 'expr field list
  | CTunion_named of string
  | CTunion_decl of string option * 'expr field list
  | CTenum_named of string
  | CTenum_decl of string option * (string * 'expr option) list
  | CTfun of 'expr parameter list * 'expr ctype

and 'expr ctype = { 
  ctype_node : 'expr ctype_node;
  ctype_storage : storage_class;
  ctype_const : bool;
  ctype_volatile : bool;
}

and 'expr parameter = 'expr ctype * string

and 'expr field = 'expr ctype * string * 'expr option

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

type 'expr c_initializer = 
  | Inothing
  | Iexpr of 'expr
  | Ilist of 'expr c_initializer list

type cstatement = cstatement_node located

and cstatement_node =
  | CSnop
  | CSexpr of cexpr
  | CScond of cexpr * cstatement * cstatement
  | CSwhile of cexpr * annot * cstatement
  | CSdowhile of cstatement * annot * cexpr
  | CSfor of cexpr * cexpr * cexpr * annot * cstatement
  | CSblock of block
  | CSreturn of cexpr option
  | CSbreak
  | CScontinue
  | CSlabel of string * cstatement
  | CSswitch of cexpr * cstatement
  | CScase of cexpr * cstatement
  | CSgoto of string
  | CSannot of annot

and block = decl located list * cstatement list

and annotated_block = annot option * block * annot option

and decl = 
  | Cspecdecl of annot
  | Ctypedef of cexpr ctype * string
  | Ctypedecl of cexpr ctype
  | Cdecl of cexpr ctype * string * cexpr c_initializer
  | Cfundef of cexpr ctype * string * cexpr parameter list * annotated_block

type file = decl located list


(*s C typed abstract syntax trees *)

open Logic

type tunary_operator = 
  | TUint_of_float | TUfloat_of_int

type tbinary_operator =
  | TBadd_int | TBsub_int | TBmul_int | TBdiv_int | TBmod_int 
  | TBadd_float | TBsub_float | TBmul_float | TBdiv_float 

type texpr = {
  texpr_node : texpr_node;
  texpr_type : texpr ctype;
  texpr_loc  : Loc.t
}

and texpr_node =
  | TEnop
  | TEconstant of string
  | TEstring_literal of string
  | TEvar of string
  | TEdot of lvalue * string
  | TEarrow of lvalue * string
  | TEarrget of lvalue * texpr
  | TEseq of texpr * texpr
  | TEassign of lvalue * assign_operator * texpr
  | TEunary of tunary_operator * texpr
  | TEbinary of texpr * tbinary_operator * texpr
  | TEcall of texpr * texpr list
  | TEcond of texpr * texpr * texpr
  | TEshift of texpr * shift * texpr
  | TEcast of texpr ctype * texpr
  | TEsizeof_expr of texpr
  | TEsizeof of texpr ctype

and lvalue = texpr (* TODO: cf CIL *)

type variant = term * pure_type * string

type loop_annotation = predicate option * variant

type loop_info = { loop_break : bool; loop_continue : bool }

type fun_info = { fun_abrupt_return : bool }

type tstatement = {
  st_node : tstatement_node;
  st_abrupt_return : bool;
  st_loc : Loc.t
}

and tstatement_node =
  | TSnop
  | TSexpr of texpr
  | TScond of texpr * tstatement * tstatement
  | TSwhile of texpr * tstatement * loop_info * loop_annotation
  | TSdowhile of tstatement * texpr * loop_info * loop_annotation
  | TSfor of texpr * texpr * texpr * tstatement * loop_info * loop_annotation
  | TSblock of tblock
  | TSreturn of texpr option
  | TSbreak
  | TScontinue
  | TSlabel of string * tstatement
  | TSswitch of texpr * tstatement
  | TScase of texpr * tstatement
  | TSgoto of string
  | TSassert of predicate

and tblock = tdecl located list * tstatement list

and annotated_tblock = predicate option * tblock * predicate option

and tdecl = 
  | Tlogic of string list * logic_type
  | Ttypedef of texpr ctype * string
  | Ttypedecl of texpr ctype
  | Tdecl of texpr ctype * string * texpr c_initializer
  | Tfundef of 
      texpr ctype * string * texpr parameter list * annotated_tblock * fun_info

type tfile = tdecl located list
