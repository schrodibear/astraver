(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: ast.mli,v 1.39 2002-07-08 09:02:28 filliatr Exp $ i*)

(*s Abstract syntax of imperative programs. *)

open Logic
open Types
open Ptree

(*s AST. ['a] is the type of information associated to the nodes. 
    ['b] is the type of predicate. *)

type variable = Ident.t

type label = string

type variant = term * pure_type * variable

type 'a t = 
  { desc : 'a t_desc;
    info : 'a }

and 'a t_desc =
  | Var of variable
  | Acc of variable
  | Aff of variable * 'a t
  | TabAcc of bool * variable * 'a t
  | TabAff of bool * variable * 'a t * 'a t
  | Seq of 'a block
  | While of 'a t * assertion option * variant * 'a t
  | If of 'a t * 'a t * 'a t
  | Lam of type_v binder list * 'a t
  | App of 'a t * 'a arg * type_c option
  | LetRef of variable * 'a t * 'a t
  | LetIn of variable * 'a t * 'a t
  | Rec of variable * type_v binder list * type_v * variant * 'a t
  | Raise of variable * 'a t option * type_v option
  | Expression of term
  | Coerce of 'a t

and 'a arg =
  | Term of 'a t
  | Refarg of variable
  | Type of type_v

and 'a block_st =
  | Label of label
  | Assert of assertion
  | Statement of 'a t

and 'a block = 'a block_st list

(*s Intermediate CC terms. *)

type cc_type =
  | TTpure of pure_type
  | TTarray of term * cc_type
  | TTlambda of cc_binder * cc_type
  | TTarrow of cc_binder * cc_type
  | TTtuple of (variable * cc_type) list * cc_type option
  | TTpred of predicate
  | TTapp of Ident.t * cc_type

and cc_bind_type = 
  | CC_var_binder of cc_type
  | CC_pred_binder of predicate
  | CC_untyped_binder

and cc_binder = variable * cc_bind_type

(* ['a] is the type of holes *)

type 'a cc_term =
  | CC_var of variable
  | CC_letin of bool * cc_binder list * 'a cc_term * 'a cc_term
  | CC_lam of cc_binder * 'a cc_term
  | CC_app of 'a cc_term * 'a cc_term
  | CC_tuple of 'a cc_term list * cc_type option
  | CC_if of 'a cc_term * 'a cc_term * 'a cc_term
  | CC_term of term
  | CC_hole of 'a
  | CC_type of cc_type

