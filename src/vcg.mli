
(*s Verification Conditions Generator. *)

open Types
open Logic
open Ast

type context_element =
  | Svar of Ident.t * cc_type
  | Spred of Ident.t * predicate

type sequent = context_element list * predicate

type obligation = string * sequent

type proof = 
  | Lemma of string * Ident.t list
  | Reflexivity of term
  | Assumption of Ident.t

type validation = proof cc_term

val vcg : string -> predicate cc_term -> obligation list * validation
