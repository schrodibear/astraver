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

(*i $Id: clogic.mli,v 1.16 2004-03-02 13:42:28 filliatr Exp $ i*)

(* AST for C annotations *)

(** abandon provisoire polymorphisme et types abstraits
type 'ctype logic_type =
  | PTctype of 'ctype
  | PTvar of 'ctype type_var
  | PTexternal of 'ctype logic_type list * string

and 'ctype type_var =
  { tag : int; mutable type_val : 'ctype logic_type option }
**)
type logic_type = 
  | LTint
  | LTfloat
  | LTarray of logic_type
  | LTpointer of logic_type
  | LTvar of string

type term_binop = Badd | Bsub | Bmul | Bdiv | Bmod
type term_unop = Uminus | Ustar

type ('ctype, 'info) term = {
  node : ('ctype, 'info) term_node;
  info : 'info
}

and ('ctype, 'info) term_node =
  | Tconstant of string
  | Tvar of Info.var_info
  | Tapp of Info.logic_info * ('ctype, 'info) term list
  | Tunop of term_unop * ('ctype, 'info) term
  | Tbinop of ('ctype, 'info) term * term_binop * ('ctype, 'info) term
  | Tdot of ('ctype, 'info) term * string
  | Tarrow of ('ctype, 'info) term * string
  | Tarrget of ('ctype, 'info) term * ('ctype, 'info) term
  | Tif of ('ctype, 'info) term * ('ctype, 'info) term * ('ctype, 'info) term
  | Told of ('ctype, 'info) term
  | Tat of ('ctype, 'info) term * string
  | Tlength of ('ctype, 'info) term
  | Tresult
  | Tnull
  | Tcast of 'ctype * ('ctype, 'info) term

type relation = Lt | Gt | Le | Ge | Eq | Neq

type 'ctype quantifiers = ('ctype * string) list

type ('term, 'ctype) predicate =
  | Pfalse
  | Ptrue
  | Papp of Loc.t * Info.logic_info * 'term list
  | Prel of 'term * relation * 'term
  | Pand of ('term, 'ctype) predicate * ('term, 'ctype) predicate
  | Por of ('term, 'ctype) predicate * ('term, 'ctype) predicate
  | Pimplies of ('term, 'ctype) predicate * ('term, 'ctype) predicate
  | Pnot of ('term, 'ctype) predicate
  | Pif of 'term * ('term, 'ctype) predicate * ('term, 'ctype) predicate
  | Pforall of 'ctype quantifiers * ('term, 'ctype) predicate
  | Pexists of 'ctype quantifiers * ('term, 'ctype) predicate
  | Pvalid of 'term * 'term * 'term

type 'term location = 
  | Lterm of 'term
  | Lstar of 'term (* e[*] *)
  | Lrange of 'term * 'term * 'term (* e[e..e] *)

type 'term variant = 'term * string option

type ('term,'pred) spec = { 
  requires : 'pred option;
  assigns : 'term location list;    
  ensures : 'pred option;
  decreases : 'term variant option
}

type ('term,'ctype) loop_annot = {
  invariant : ('term,'ctype) predicate option;
  variant : 'term variant option
}

type ('term,'ctype) logic_symbol =
  | Predicate_reads of 'ctype list * 'term location list
  | Predicate_def of 'ctype list * ('term,'ctype) predicate 
  | Function of 'ctype list * 'ctype * 'term location list
