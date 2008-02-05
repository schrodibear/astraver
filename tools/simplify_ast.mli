(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann R�GIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
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
