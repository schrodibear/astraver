(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: ast.mli,v 1.43 2002-09-06 11:56:52 filliatr Exp $ i*)

(*s Abstract syntax of imperative programs. *)

open Logic
open Types
open Ptree

type variable = Ident.t

type label = string

type variant = term * pure_type * variable

(* ['a] is the type of information associated to the nodes. *)

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
  | App of 'a t * 'a arg * type_c
  | LetRef of variable * 'a t * 'a t
  | LetIn of variable * 'a t * 'a t
  | Rec of variable * type_v binder list * type_v * variant * 'a t
  | Raise of variable * 'a t option
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

