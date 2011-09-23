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

(* Functional programs. *)

type cc_functional_program = (Loc.position * predicate) cc_term

(*s Sequents and obligations. *)

type context_element =
  | Svar of Ident.t * pure_type
  | Spred of Ident.t * predicate

type sequent = context_element list * predicate

type loc_term = Loc.position * term
type loc_predicate = Loc.position * predicate

type assert_kind = [`ASSERT | `CHECK]

type raw_vc_explain =
  | VCEexternal of string
  | VCEabsurd
  | VCEassert of assert_kind * loc_predicate list
  | VCEpre of string * Loc.position * loc_predicate list 
      (*r label and loc for the call, then preconditions *)
  | VCEpost of loc_predicate
  | VCEwfrel
  | VCEvardecr of loc_term
  | VCEinvinit of string * loc_predicate
      (*r label for the loop, then loop invariant *)
  | VCEinvpreserv of string * loc_predicate 
      (*r label for the loop, then loop invariant *)

(*
type obligation = Loc.floc * vc_explain * string * sequent
    (* loc, explanation, id, sequent *) 
*)

