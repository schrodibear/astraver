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

(*i $Id: clogic.mli,v 1.3 2004-01-14 10:57:24 filliatr Exp $ i*)

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
  | Tif of 'a term * 'a term * 'a term

type relation = Lt | Gt | Le | Ge | Eq | Neq

type 'a predicate = ('a predicate_node, 'a) info

and 'a predicate_node =
  | Pfalse
  | Ptrue
  | Pvar of string
  | Prel of 'a term * relation * 'a term
  | Pand of 'a predicate * 'a predicate
  | Por of 'a predicate * 'a predicate
  | Pimplies of 'a predicate * 'a predicate
  | Pnot of 'a predicate
  | Papp of string * 'a term list
  | Pif of 'a term * 'a predicate * 'a predicate
  | Pforall of string * pure_type * 'a predicate
  | Pexists of string * pure_type * 'a predicate

type effects = string list * string list

type 'a spec = 'a predicate option * effects * 'a predicate option

type 'a annot_statement = Assert of 'a predicate | Label of string

type 'a variant = 'a term * string option

type 'a loop_annot = 'a predicate option * 'a variant

