
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: ast.mli,v 1.1 2001-08-15 21:08:51 filliatr Exp $ *)

(*s Abstract syntax of imperative programs. *)

open Logic
open Types

type termination = 
  | RecArg of int 
  | Wf of term * term

type variable = Ident.t

(*i
type pattern =
  | PatVar of Ident.t
  | PatConstruct of Ident.t * ((section_path * int) * int)
  | PatAlias of pattern * Ident.t
  | PatPair of pattern * pattern
  | PatApp of pattern list

type epattern =
  | ExnConstant of Ident.t
  | ExnBind of Ident.t * Ident.t
i*)

(*s Blocks. *)

type 'a block_st =
  | Label of string
  | Assert of assertion
  | Statement of 'a

type 'a block = 'a block_st list

(*s AST. ['a] is the type of information associated to the nodes. *)

type 'a t = 
  { desc : 'a t_desc;
    pre  : precondition list;
    post : postcondition option;
    loc  : Location.t;
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
  | App of 'a t * 'a arg list
  | SApp of 'a t_desc list * 'a t list
  | LetRef of variable * 'a t * 'a t
  | LetIn of variable * 'a t * 'a t
  | LetRec of variable * type_v binder list * type_v * (term * term) * 'a t
  | PPoint of string * 'a t_desc
  | Expression of term
  | Debug of string * 'a t

and 'a arg =
  | Term of 'a t
  | Refarg of variable
  | Type of type_v

type parsed_program = unit t

(*s Intermediate type for CC terms. *)

type cc_type =
  | TTpure of pure_type
  | TTarrow of cc_type binder list 
  | TTarray of term * cc_type

type cc_bind_type = 
  | CC_typed_binder of cc_type 
  | CC_untyped_binder

type cc_binder = variable * cc_bind_type

type cc_term =
  | CC_var of variable
  | CC_letin of bool * cc_type * cc_binder list * cc_term * cc_term
  | CC_lam of cc_binder list * cc_term
  | CC_app of cc_term * cc_term list
  | CC_tuple of bool * cc_type list * cc_term list
  | CC_case of cc_type * cc_term * cc_term list
  | CC_expr of term
  | CC_hole of predicate
