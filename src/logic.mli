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

(*i $Id: logic.mli,v 1.12 2002-11-05 08:19:32 filliatr Exp $ i*)

(*s Logic. *)

type constant =
  | ConstInt of int
  | ConstBool of bool
  | ConstUnit
  | ConstFloat of string

type term =
  | Tvar of Ident.t
  | Tconst of constant
  | Tderef of Ident.t
  | Tapp of Ident.t * term list

type substitution = term Ident.map
type var_substitution = Ident.t Ident.map

(*s Pure types. *)

type pure_type =
  | PTint
  | PTbool
  | PTfloat
  | PTunit
  | PTarray of term * pure_type
  | PTexternal of Ident.t

type predicate =
  | Pvar of Ident.t
  | Papp of Ident.t * term list
  | Ptrue
  | Pfalse
  | Pimplies of predicate * predicate
  | Pif of term * predicate * predicate
  | Pand of predicate * predicate
  | Por of predicate * predicate
  | Pnot of predicate
  | Forall of Ident.t * Ident.t * pure_type * predicate
  | Exists of Ident.t * Ident.t * pure_type * predicate

type logic_type =
  | Predicate of pure_type list
  | Function of pure_type list * pure_type
