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

(*i $Id: clogic.mli,v 1.6 2004-02-09 15:57:21 filliatr Exp $ i*)

(* AST for C annotations *)

type pure_type =
  | PTint
  | PTfloat
  | PTarray of pure_type
  | PTvarid of string
  | PTvar of type_var
  | PTexternal of pure_type list * string

and type_var =
  { tag : int; mutable type_val : pure_type option }

type logic_type =
  | Predicate of pure_type list
  | Function of pure_type list * pure_type

type label = Current | Before | At of string


type ('a, 'b) info = { node : 'a; info : 'b }

type term_binop = Badd | Bsub | Bmul | Bdiv | Bmod
type term_unop = Uminus | Ustar

type 'a term = ('a term_node, 'a) info

and 'a term_node =
  | Tconstant of string
  | Tvar of string * label
  | Tapp of string * 'a term list
  | Tunop of term_unop * 'a term
  | Tbinop of 'a term * term_binop * 'a term
  | Tdot of 'a term * string
  | Tarrow of 'a term * string
  | Tarrget of 'a term * 'a term
  | Tif of 'a term * 'a term * 'a term
  | Told of 'a term
  | Tat of 'a term * string

type relation = Lt | Gt | Le | Ge | Eq | Neq

type ('term, 'ident) predicate =
  | Pfalse
  | Ptrue
  | Pvar of 'ident
  | Papp of 'ident * 'term list
  | Prel of 'term * relation * 'term
  | Pand of ('term, 'ident) predicate * ('term, 'ident) predicate
  | Por of ('term, 'ident) predicate * ('term, 'ident) predicate
  | Pimplies of ('term, 'ident) predicate * ('term, 'ident) predicate
  | Pnot of ('term, 'ident) predicate
  | Pif of 'term * ('term, 'ident) predicate * ('term, 'ident) predicate
  | Pforall of string * pure_type * ('term, 'ident) predicate
  | Pexists of string * pure_type * ('term, 'ident) predicate

type location = 
  | Lid of string

type modifiable = location list

type 'pred spec = 'pred option * modifiable * 'pred option

type 'term variant = 'term * string option

type ('term,'ident) loop_annot = 
  ('term,'ident) predicate option * 'term variant

(* parsed AST *)

type parsed_predicate = (Loc.t term, (string, Loc.t) info) predicate
type parsed_spec = parsed_predicate spec
type parsed_loop_annot = (Loc.t term, (string, Loc.t) info) loop_annot

type parsed_decl = 
  | LDlogic of string * pure_type * (pure_type * string) list
  | LDpredicate of string * (pure_type * string) list
  | LDaxiom of string * parsed_predicate

type parsed_code_annot = Assert of parsed_predicate | Label of string

type parsed_annot = 
  | Adecl of parsed_decl
  | Aspec of parsed_spec
  | Acode_annot of parsed_code_annot
  | Aloop_annot of parsed_loop_annot

