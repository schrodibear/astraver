
(*s Verification Conditions Generator. *)

open Types
open Logic
open Ast

type context_element =
  | Svar of Ident.t * cc_type
  | Spred of predicate

type sequent = context_element list * predicate

type obligation = string * sequent

val vcg : string -> cc_term -> obligation list
