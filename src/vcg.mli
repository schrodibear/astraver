
(*s Verification Conditions Generator. *)

open Types
open Logic
open Cc

type context_element =
  | Svar of Ident.t * cc_type
  | Spred of Ident.t * predicate

type sequent = context_element list * predicate

type obligation = string * sequent

type proof = 
  | Lemma of string * Ident.t list
  | True
  | Reflexivity of term
  | Assumption of Ident.t
  | Proj1 of Ident.t
  | Conjunction of Ident.t * Ident.t

type validation = proof cc_term

val vcg : string -> predicate cc_term -> obligation list * validation
