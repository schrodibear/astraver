(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: ast.mli,v 1.16 2002-03-12 16:05:24 filliatr Exp $ i*)

(*s Abstract syntax of imperative programs. *)

open Logic
open Types

(*s Blocks. *)

type label = string

type 'a block_st =
  | Label of label
  | Assert of assertion
  | Statement of 'a

type 'a block = 'a block_st list

(*s AST. ['a] is the type of information associated to the nodes. *)

type variable = Ident.t

type 'a t = 
  { desc : 'a t_desc;
    info : 'a }

and 'a t_desc =
  | Var of variable
  | Acc of variable
  | Aff of variable * 'a t
  | TabAcc of bool * variable * 'a t
  | TabAff of bool * variable * 'a t * 'a t
  | Seq of 'a t block
  | While of 'a t * assertion option * (term * term) * 'a t block
  | If of 'a t * 'a t * 'a t
  | Lam of type_v binder list * 'a t
  | App of 'a t * 'a arg
  | LetRef of variable * 'a t * 'a t
  | LetIn of variable * 'a t * 'a t
  | LetRec of variable * type_v binder list * type_v * (term * term) * 'a t
  | Expression of term
  | Coerce of 'a t

and 'a arg =
  | Term of 'a t
  | Refarg of Loc.t * variable
  | Type of type_v

type parsed_info = {
  pre  : precondition list;
  post : postcondition option;
  loc  : Loc.t }

type parsed_program = parsed_info t

(*s Declarations. *)

type decl = 
  | Program of Ident.t * parsed_program
  | External of Loc.t * Ident.t list * type_v
  | QPvs of string

(*s Intermediate type for CC terms. *)

type cc_type =
  | TTpure of pure_type
  | TTarray of term * cc_type
  | TTarrow of cc_binder * cc_type
  | TTtuple of (variable * cc_type) list * predicate option

and cc_bind_type = 
  | CC_var_binder of cc_type
  | CC_pred_binder of predicate
  | CC_untyped_binder

and cc_binder = variable * cc_bind_type

type cc_term =
  | CC_var of variable
  | CC_letin of bool * cc_binder list * cc_term * cc_term
  | CC_lam of cc_binder list * cc_term
  | CC_app of cc_term * cc_term list
  | CC_tuple of cc_term list
  | CC_case of cc_term * (cc_binder list * cc_term) list
  | CC_if of cc_term * cc_term * cc_term
  | CC_expr of term
  | CC_hole of predicate
