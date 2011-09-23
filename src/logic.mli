(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)



(*s Logic. *)

type real_constant = 
  | RConstDecimal of string * string * string option (* int / frac / exp *)
  | RConstHexa of string * string * string

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
    user : bool;
    mutable type_val : pure_type option }

type instance = pure_type list

type term_label = User of string | Internal of int

type term =
  | Tconst of constant
  | Tvar of Ident.t
  | Tderef of Ident.t
  | Tapp of Ident.t * term list * instance
  | Tnamed of term_label * term

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
  | Pnamed of term_label * predicate
  | Plet of Ident.t * Ident.t * pure_type * term * predicate

and pattern = TPat of term | PPat of predicate
and trigger = pattern list
and triggers = trigger list


type logic_type =
  | Predicate of pure_type list
  | Function of pure_type list * pure_type

type alg_type_def = pure_type list * (Ident.t * pure_type list) list

type predicate_def = (Ident.t * pure_type) list * predicate

type inductive_def = pure_type list * (Ident.t * predicate) list

type function_def = (Ident.t * pure_type) list * pure_type * term


