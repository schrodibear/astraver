(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: ast.mli,v 1.38 2002-07-05 16:14:09 filliatr Exp $ i*)

(*s Abstract syntax of imperative programs. *)

open Logic
open Types

(*s AST. ['a] is the type of information associated to the nodes. 
    ['b] is the type of predicate. *)

type variable = Ident.t

type label = string

type variant = term * pure_type * term

type ('a,'b) t = 
  { desc : ('a,'b) t_desc;
    info : 'a }

and ('a,'b) t_desc =
  | Var of variable
  | Acc of variable
  | Aff of variable * ('a,'b) t
  | TabAcc of bool * variable * ('a,'b) t
  | TabAff of bool * variable * ('a,'b) t * ('a,'b) t
  | Seq of ('a,'b) block
  | While of ('a,'b) t * 'b asst option * variant * ('a,'b) t
  | If of ('a,'b) t * ('a,'b) t * ('a,'b) t
  | Lam of 'b ptype_v binder list * ('a,'b) t
  | App of ('a,'b) t * ('a,'b) arg * 'b ptype_c option
  | LetRef of variable * ('a,'b) t * ('a,'b) t
  | LetIn of variable * ('a,'b) t * ('a,'b) t
  | Rec of variable * 'b ptype_v binder list * 'b ptype_v * variant * ('a,'b) t
  | Raise of variable * ('a,'b) t option * 'b ptype_v option
  | Expression of term
  | Coerce of ('a,'b) t

and ('a,'b) arg =
  | Term of ('a,'b) t
  | Refarg of variable
  | Type of 'b ptype_v

and ('a,'b) block_st =
  | Label of label
  | Assert of 'b asst
  | Statement of ('a,'b) t

and ('a,'b) block = ('a,'b) block_st list

(*s parsed predicates *)

type pp_infix = 
  PPand | PPor | PPimplies | 
  PPlt | PPle | PPgt | PPge | PPeq | PPneq |
  PPadd | PPsub | PPmul | PPdiv | PPmod

type pp_prefix = 
  PPneg | PPnot

type ppredicate = 
  { pp_loc : Loc.t; pp_desc : pp_desc }

and pp_desc =
  | PPvar of variable
  | PPapp of variable * ppredicate list
  | PPtrue
  | PPfalse
  | PPconst of constant
  | PPinfix of ppredicate * pp_infix * ppredicate
  | PPprefix of pp_prefix * ppredicate
  | PPif of ppredicate * ppredicate * ppredicate
  | PPforall of Ident.t * pure_type * ppredicate

(*s The parsing information consists of pre/post-conditions and location
    in the source file. *)

type parsed_info = {
  pre  : ppredicate pre list;
  post : ppredicate post option;
  loc  : Loc.t }

type parsed_program = (parsed_info, ppredicate) t

type parsed_type_v = ppredicate ptype_v
type parsed_type_c = ppredicate ptype_c

(*s Declarations. *)

type decl = 
  | Program of Ident.t * parsed_program
  | Parameter of Loc.t * Ident.t list * parsed_type_v
  | External of Loc.t * Ident.t list * parsed_type_v
  | Exception of Loc.t * Ident.t * pure_type option
  | Logic of Loc.t * Ident.t * logic_type
  | QPvs of string

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

