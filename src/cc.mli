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

(*i $Id: cc.mli,v 1.9 2002-11-12 14:35:02 filliatr Exp $ i*)

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
  | TTapp of cc_type * cc_type list
  | TTterm of term

and cc_bind_type = 
  | CC_var_binder of cc_type
  | CC_pred_binder of predicate
  | CC_untyped_binder

and cc_binder = variable * cc_bind_type

type cc_pattern = 
  | PPvariable of cc_binder
  | PPcons of Ident.t * cc_pattern list

(* ['a] is the type of holes *)

type 'a cc_term =
  | CC_var of variable
  | CC_letin of bool * cc_binder list * 'a cc_term * 'a cc_term
  | CC_lam of cc_binder * 'a cc_term
  | CC_app of 'a cc_term * 'a cc_term
  | CC_tuple of 'a cc_term list * cc_type option
  | CC_if of 'a cc_term * 'a cc_term * 'a cc_term
  | CC_case of 'a cc_term * (cc_pattern * 'a cc_term) list
  | CC_term of term
  | CC_hole of 'a
  | CC_type of cc_type
