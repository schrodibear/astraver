(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(*i $Id: ast.mli,v 1.49 2004-03-11 14:39:26 filliatr Exp $ i*)

(*s Abstract syntax of imperative programs. *)

open Logic
open Types
open Ptree

type variable = Ident.t

type label = string

type variant = term * pure_type * variable

type exn_pattern = Ptree.exn_pattern

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
  | Try of 'a t * (exn_pattern * 'a t) list 
  | Expression of term
  | Absurd
  | Any of type_c

and 'a arg =
  | Term of 'a t
  | Refarg of variable
  | Type of type_v

and 'a block_st =
  | Label of label
  | Assert of assertion
  | Statement of 'a t

and 'a block = 'a block_st list

