(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: cc.mli,v 1.5 2002-10-09 18:00:45 filliatr Exp $ i*)

(*s Intermediate CC terms. *)

open Logic

type variable = Ident.t

type cc_type =
  | TTpure of pure_type
  | TTarray of term * cc_type
  | TTlambda of cc_binder * cc_type
  | TTarrow of cc_binder * cc_type
  | TTtuple of cc_binder list * cc_type option
  | TTpred of predicate
  | TTapp of Ident.t * cc_type list

and cc_bind_type = 
  | CC_var_binder of cc_type
  | CC_pred_binder of predicate
  | CC_untyped_binder

and cc_binder = variable * cc_bind_type

type cc_pattern = 
  | PPvariable of variable * cc_type
  | PPcons of Ident.t * cc_pattern list

type case_pred = variable * int

(* ['a] is the type of holes *)

type 'a cc_term =
  | CC_var of variable
  | CC_letin of bool * cc_binder list * 'a cc_term * 'a cc_term
  | CC_lam of cc_binder * 'a cc_term
  | CC_app of 'a cc_term * 'a cc_term
  | CC_tuple of 'a cc_term list * cc_type option
  | CC_if of 'a cc_term * 'a cc_term * 'a cc_term
  | CC_case of variable * case_pred option * (cc_pattern * 'a cc_term) list
  | CC_term of term
  | CC_hole of 'a
  | CC_type of cc_type
