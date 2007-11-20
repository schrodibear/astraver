(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2007                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
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

(*i $Id: cc.mli,v 1.23 2007-11-20 14:34:51 filliatr Exp $ i*)

(*s Intermediate CC terms. *)

open Logic

type variable = Ident.t

type cc_type =
  | TTpure of pure_type
  | TTarray of cc_type
  | TTlambda of cc_binder * cc_type
  | TTarrow of cc_binder * cc_type
  | TTtuple of cc_binder list * cc_type option
  | TTpred of predicate
  | TTapp of cc_type * cc_type list
  | TTterm of term
  | TTSet

and cc_bind_type = 
  | CC_var_binder of cc_type
  | CC_pred_binder of predicate
  | CC_untyped_binder

and cc_binder = variable * cc_bind_type

type cc_pattern = 
  | PPvariable of cc_binder
  | PPcons of Ident.t * cc_pattern list

(* ['a] is the type of holes *)

type 'a cc_term =
  | CC_var of variable
  | CC_letin of bool * cc_binder list * 'a cc_term * 'a cc_term
  | CC_lam of cc_binder * 'a cc_term
  | CC_app of 'a cc_term * 'a cc_term
  | CC_tuple of 'a cc_term list * cc_type option
  | CC_if of 'a cc_term * 'a cc_term * 'a cc_term
  | CC_case of 'a cc_term * (cc_pattern * 'a cc_term) list
  | CC_term of term
  | CC_hole of 'a
  | CC_type of cc_type
  | CC_any of cc_type

(* Proofs *)

type proof = 
  | Lemma of string * Ident.t list
  | True
  | Reflexivity of term
  | Assumption of Ident.t
  | Proj1 of Ident.t
  | Proj2 of Ident.t
  | Conjunction of Ident.t * Ident.t
  | WfZwf of term
  | Loop_variant_1 of Ident.t * Ident.t
  | Absurd of Ident.t
  | ProofTerm of proof cc_term
  | ShouldBeAWp

type proof_term = proof cc_term

type validation = proof cc_term


(*s Sequents and obligations. *)

type context_element =
  | Svar of Ident.t * pure_type
  | Spred of Ident.t * predicate

type sequent = context_element list * predicate

type loc_predicate = Loc.position * predicate

type vc_explain =
  | VCEstring of string
  | VCEexternal of string
  | VCEabsurd
  | VCEassert of loc_predicate list
  | VCEpre of string * loc_predicate list 
  | VCEpost of loc_predicate
  | VCEwfrel
  | VCEvardecr 
  | VCEinvinit of loc_predicate
  | VCEinvpreserv of loc_predicate 

type obligation = Loc.position * vc_explain * string * sequent
    (* loc, explanation, id, sequent *) 
