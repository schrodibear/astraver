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

(*i $Id: clogic.mli,v 1.14 2004-02-24 08:15:23 filliatr Exp $ i*)

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

type ('a, 'b) info = { node : 'a; info : 'b }

type term_binop = Badd | Bsub | Bmul | Bdiv | Bmod
type term_unop = Uminus | Ustar

type 'a term = ('a term_node, 'a) info

and 'a term_node =
  | Tconstant of string
  | Tvar of string
  | Tapp of string * 'a term list
  | Tunop of term_unop * 'a term
  | Tbinop of 'a term * term_binop * 'a term
  | Tdot of 'a term * string
  | Tarrow of 'a term * string
  | Tarrget of 'a term * 'a term
  | Tif of 'a term * 'a term * 'a term
  | Told of 'a term
  | Tat of 'a term * string
  | Tlength of 'a term
  | Tresult
  | Tnull

type relation = Lt | Gt | Le | Ge | Eq | Neq

type 'ctype quantifiers = ('ctype * string) list

type ('term, 'ctype) predicate =
  | Pfalse
  | Ptrue
  | Pvar of Loc.t * string
  | Papp of Loc.t * string * 'term list
  | Prel of 'term * relation * 'term
  | Pand of ('term, 'ctype) predicate * ('term, 'ctype) predicate
  | Por of ('term, 'ctype) predicate * ('term, 'ctype) predicate
  | Pimplies of ('term, 'ctype) predicate * ('term, 'ctype) predicate
  | Pnot of ('term, 'ctype) predicate
  | Pif of 'term * ('term, 'ctype) predicate * ('term, 'ctype) predicate
  | Pforall of 'ctype quantifiers * ('term, 'ctype) predicate
  | Pexists of 'ctype quantifiers * ('term, 'ctype) predicate

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
  | Function of 'ctype list * 'ctype
