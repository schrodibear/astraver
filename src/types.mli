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

(*i $Id: types.mli,v 1.16 2002-12-04 10:29:51 filliatr Exp $ i*)

(*s Types for programs *)

open Logic

(*s Pre- and postconditions. *)

type 'a asst = { a_name : Ident.name; a_value : 'a }

type assertion = predicate asst

type 'a post = 'a asst * (Ident.t * 'a asst) list

type precondition = assertion

type postcondition = assertion * (Ident.t * assertion) list

(*s Binders. *)

type 'a binder_type =
  | BindType of 'a
  | BindSet
  | Untyped

type 'a binder = Ident.t * 'a binder_type

(*s Types of values ([type_v]) and computations ([type_c]) *)

type type_v = 
  | Ref of type_v
  | Array of type_v
  | Arrow of type_v binder list * type_c
  | PureType of pure_type

and type_c = 
  { c_result_name : Ident.t;
    c_result_type : type_v;
    c_effect : Effect.t;
    c_pre    : precondition list;
    c_post   : postcondition option }

