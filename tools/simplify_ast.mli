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

type term = 
  | Tconst of string (* int constant *)
  | Tapp of string * term list

type trigger = term list

type rel = Eq | Neq | Lt | Le | Gt | Ge

type predicate = 
  | Ptrue
  | Pfalse
  | Prel of term * rel * term
  | Pnot of predicate
  | Pand of predicate list
  | Por of predicate list
  | Pimplies of predicate * predicate
(*
  | Pexplies of predicate * predicate
*)
  | Piff of predicate * predicate
  | Pdistinct of term list
  | Pforall of string list * trigger list * predicate
  | Pexists of string list * trigger list * predicate
  | Plblpos of string * predicate
  | Plblneg of string * predicate

type decl =
  | Axiom of predicate
  | Goal of predicate
  | Defpred of string * string list * predicate

type t = decl list
