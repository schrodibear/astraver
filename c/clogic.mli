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

(*i $Id: clogic.mli,v 1.36 2004-10-21 14:52:45 hubert Exp $ i*)

(* AST for C annotations *)

type logic_type = 
  | LTint
  | LTfloat
  | LTarray of logic_type
  | LTpointer of logic_type
  | LTvar of string

(* parsed terms and predicates *)

type constant = IntConstant of string | FloatConstant of string

type term_binop = Badd | Bsub | Bmul | Bdiv | Bmod
type term_unop = Uminus | Ustar | Uamp | Ufloat_of_int

type 'ctype quantifiers = ('ctype * string) list
type 'ctype typed_quantifiers = ('ctype * Info.var_info) list

type relation = Lt | Gt | Le | Ge | Eq | Neq

type lexpr = {
  lexpr_node : lexpr_node;
  lexpr_loc : Loc.t
}

and lexpr_node = 
  (* both terms and predicates *)
  | PLvar of Info.var_info
  | PLapp of Info.logic_info * lexpr list
  (* terms *)
  | PLconstant of constant
  | PLunop of term_unop * lexpr
  | PLbinop of lexpr * term_binop * lexpr
  | PLdot of lexpr * string
  | PLarrow of lexpr * string
  | PLarrget of lexpr * lexpr
  | PLold of lexpr
  | PLat of lexpr * string
  | PLbase_addr of lexpr
  | PLblock_length of lexpr
  | PLresult
  | PLnull
  | PLcast of logic_type * lexpr
  (* predicates *)
  | PLfalse
  | PLtrue
  | PLrel of lexpr * relation * lexpr
  | PLand of lexpr * lexpr
  | PLor of lexpr * lexpr
  | PLimplies of lexpr * lexpr
  | PLiff of lexpr * lexpr
  | PLnot of lexpr
  | PLif of lexpr * lexpr * lexpr
  | PLforall of logic_type quantifiers * lexpr
  | PLexists of logic_type quantifiers * lexpr
  | PLvalid of lexpr
  | PLvalid_index of lexpr * lexpr
  | PLvalid_range of lexpr * lexpr * lexpr
  | PLfresh of lexpr

(* typed terms *)

type 'ctype term = {
  term_node : 'ctype term_node;
  term_loc : Loc.t;
  term_type : 'ctype
}

and 'ctype term_node =
  | Tconstant of constant
  | Tvar of Info.var_info
  | Tapp of Info.logic_info * 'ctype term list
  | Tunop of term_unop * 'ctype term
  | Tbinop of 'ctype term * term_binop * 'ctype term
  | Tdot of 'ctype term * Info.var_info
  | Tarrow of 'ctype term * Info.var_info
  | Tarrget of 'ctype term * 'ctype term
  | Tif of 'ctype term * 'ctype term * 'ctype term
  | Told of 'ctype term
  | Tat of 'ctype term * string
  | Tbase_addr of 'ctype term
  | Tblock_length of 'ctype term
  | Tresult
  | Tnull
  | Tcast of 'ctype * 'ctype term

(* typed predicates *)

type 'ctype predicate =
  | Pfalse
  | Ptrue
  | Papp of Info.logic_info * 'ctype term list
  | Prel of 'ctype term * relation * 'ctype term
  | Pand of 'ctype predicate * 'ctype predicate
  | Por of 'ctype predicate * 'ctype predicate
  | Pimplies of 'ctype predicate * 'ctype predicate
  | Piff of 'ctype predicate * 'ctype predicate
  | Pnot of 'ctype predicate
  | Pif of 'ctype term * 'ctype predicate * 'ctype predicate
  | Pforall of 'ctype typed_quantifiers * 'ctype predicate
  | Pexists of 'ctype typed_quantifiers * 'ctype predicate
  | Pold of 'ctype predicate
  | Pat of 'ctype predicate * string
  | Pvalid of 'ctype term 
  | Pvalid_index of 'ctype term * 'ctype term
  | Pvalid_range of 'ctype term * 'ctype term * 'ctype term
  | Pfresh of 'ctype term 
  | Palloc_extends

type 'term location = 
  | Lterm of 'term
  | Lstar of 'term (* e[*] *)
  | Lrange of 'term * 'term * 'term (* e[e..e] *)

(* should be :
  | Lvar of Info.var_info
  | Larrget of 'term location * 'term
  | Larrow of 'term location * Info.field_info
  | Ldot of 'term location * Info.field_info
  | Lrange of 'term location * 'term * 'term (* l[e..e] *)
  | Lallrange of 'term location  (* l[*] *)
  | Lstar of 'term location (* *l *)
*)

type 'term variant = 'term * string option

type ('term,'pred) spec = { 
  mutable requires : 'pred option;
  mutable assigns : 'term location list option;    
  mutable ensures : 'pred option;
  mutable decreases : 'term variant option
}

type ('term,'pred) loop_annot = {
  invariant : 'pred option;
  loop_assigns : 'term location list option;
  variant : 'term variant option
}

type ('term,'ctype) logic_symbol =
  | Predicate_reads of (Info.var_info * 'ctype) list * 'term location list
  | Predicate_def of (Info.var_info * 'ctype) list * 'ctype predicate 
  | Function of (Info.var_info * 'ctype) list * 'ctype * 'term location list
