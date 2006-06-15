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

(*i $Id: logic.mli,v 1.35 2006-06-15 09:58:30 lescuyer Exp $ i*)

(*s Logic. *)

type real_constant = string * string * string (* int / frac / exp *)

type constant =
  | ConstInt of string
  | ConstBool of bool
  | ConstUnit
  | ConstFloat of real_constant

(*s Pure types. *)

type pure_type =
  | PTint
  | PTbool
  | PTreal
  | PTunit
  | PTvar of type_var
  | PTexternal of pure_type list * Ident.t

and type_var =
  { tag : int; 
    mutable type_val : pure_type option }

type instance = pure_type list

type term =
  | Tconst of constant
  | Tvar of Ident.t
  | Tderef of Ident.t
  | Tapp of Ident.t * term list * instance

type substitution = term Ident.map
type var_substitution = Ident.t Ident.map

type is_wp = bool
type is_sym = bool

type predicate =
  | Pvar of Ident.t
  | Papp of Ident.t * term list * instance
  | Ptrue
  | Pfalse
  | Pimplies of is_wp * predicate * predicate
  | Pif of term * predicate * predicate
  | Pand of is_wp * is_sym * predicate * predicate
  | Por of predicate * predicate
  | Piff of predicate * predicate
  | Pnot of predicate
  | Forall of is_wp * Ident.t * Ident.t * pure_type * triggers * predicate
  | Forallb of is_wp * predicate * predicate
  | Exists of Ident.t * Ident.t * pure_type * predicate
  | Pfpi of term * real_constant * real_constant
  | Pnamed of string * predicate
and pattern = TPat of term | PPat of predicate
and trigger = pattern list
and triggers = trigger list


type logic_type =
  | Predicate of pure_type list
  | Function of pure_type list * pure_type

type predicate_def = (Ident.t * pure_type) list * predicate

type function_def = (Ident.t * pure_type) list * pure_type * term


