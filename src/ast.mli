(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: ast.mli,v 1.29 2002-05-07 15:53:23 filliatr Exp $ i*)

(*s Abstract syntax of imperative programs. *)

open Logic
open Types

(*s AST. ['a] is the type of information associated to the nodes. *)

type variable = Ident.t

type label = string

type variant = term * term

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
  | Expression of term
  | Coerce of 'a t

and 'a arg =
  | Term of 'a t
  | Refarg of Loc.t * variable
  | Type of type_v

and 'a block_st =
  | Label of label
  | Assert of assertion
  | Statement of 'a t

and 'a block = 'a block_st list

(*s The parsing information consists of pre/post-conditions and location
    in the source file. *)

type parsed_info = {
  pre  : precondition list;
  post : postcondition option;
  loc  : Loc.t }

type parsed_program = parsed_info t

(*s Declarations. *)

type decl = 
  | Program of Ident.t * parsed_program
  | Parameter of Loc.t * Ident.t list * type_v
  | External of Loc.t * Ident.t list * type_v
  | QPvs of string

(*s Intermediate CC terms. *)

type cc_type =
  | TTpure of pure_type
  | TTarray of term * cc_type
  | TTlambda of cc_binder * cc_type
  | TTarrow of cc_binder * cc_type
  | TTtuple of (variable * cc_type) list * cc_type option
  | TTpred of predicate

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
  | CC_case of 'a cc_term * (cc_binder list * 'a cc_term) list
  | CC_if of 'a cc_term * 'a cc_term * 'a cc_term
  | CC_term of term
  | CC_hole of 'a
  | CC_type of cc_type
