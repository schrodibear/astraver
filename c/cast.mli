(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filli�tre - Claude March�
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

(*i $Id: cast.mli,v 1.16 2004-01-14 10:57:24 filliatr Exp $ i*)

(*s C types *)

type 'a located = { node : 'a; loc : Loc.t }

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
  | CTstruct of string * 'expr field list
  | CTunion_named of string
  | CTunion of string * 'expr field list
  | CTenum_named of string
  | CTenum of string * (string * 'expr option) list
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

type annot = int * string

type assign_operator = 
  | Aequal | Amul | Adiv | Amod | Aadd | Asub | Aleft | Aright 
  | Aand | Axor | Aor

type unary_operator = 
  | Uprefix_inc | Uprefix_dec | Upostfix_inc | Upostfix_dec 
  | Uplus | Uminus | Unot | Ustar | Uamp | Utilde
  (* these are introduced during typing *)
  | Ufloat_of_int | Uint_of_float

type binary_operator =
  | Badd | Bsub | Bmul | Bdiv | Bmod 
  | Blt | Bgt | Ble | Bge | Beq | Bneq 
  | Bbw_and | Bbw_xor | Bbw_or | Band | Bor
  | Bshift_left | Bshift_right
  (* these are introduced during typing *)
  | Badd_int | Bsub_int | Bmul_int | Bdiv_int | Bmod_int 
  | Badd_float | Bsub_float | Bmul_float | Bdiv_float 
  | Badd_pointer_int (* pointer + int *) 
  | Badd_int_pointer (* int + pointer *)
  | Bsub_pointer_int (* pointer - int *)
  | Bsub_pointer     (* pointer - pointer *)

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
  | CSif of cexpr * cstatement * cstatement
  | CSwhile of cexpr * annot option * cstatement
  | CSdowhile of cstatement * annot option * cexpr
  | CSfor of cexpr * cexpr * cexpr * annot option * cstatement
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

open Clogic

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
  | TEunary of unary_operator * texpr
  | TEbinary of texpr * binary_operator * texpr
  | TEcall of texpr * texpr list
  | TEcond of texpr * texpr * texpr
  | TEcast of texpr ctype * texpr
  | TEsizeof_expr of texpr
  | TEsizeof of texpr ctype

and lvalue = texpr (* TODO: cf CIL *)

type tctype = texpr ctype

type variant = tctype term * string option

type loop_annotation = tctype predicate option * variant

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
  | TSif of texpr * tstatement * tstatement
  | TSwhile of texpr * tstatement * loop_info * loop_annotation option
  | TSdowhile of tstatement * texpr * loop_info * loop_annotation option
  | TSfor of 
      texpr * texpr * texpr * tstatement * loop_info * loop_annotation option
  | TSblock of tblock
  | TSreturn of texpr option
  | TSbreak
  | TScontinue
  | TSlabel of string * tstatement
  | TSswitch of texpr * tstatement
  | TScase of texpr * tstatement
  | TSgoto of string
  | TSassert of tctype predicate

and tblock = tdecl located list * tstatement list

and annotated_tblock = 
    tctype predicate option * tblock * tctype predicate option

and tdecl = 
  | Tlogic of string list * logic_type
  | Ttypedef of texpr ctype * string
  | Ttypedecl of texpr ctype
  | Tdecl of texpr ctype * string * texpr c_initializer
  | Tfundef of 
      texpr ctype * string * texpr parameter list * annotated_tblock * fun_info

type tfile = tdecl located list
