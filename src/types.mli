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

(*i $Id: types.mli,v 1.18 2005-11-03 14:11:37 filliatr Exp $ i*)

(*s Types for programs.
    Types of values ([type_v]) and computations ([type_c]) *)

open Logic

type assertion = predicate

type precondition = assertion

type postcondition = assertion * (Ident.t * assertion) list

type 'a binder = Ident.t * 'a

type type_v = 
  | PureType of pure_type
  | Ref of pure_type
  | Arrow of type_v binder list * type_c

and type_c = 
  { c_result_name : Ident.t;
    c_result_type : type_v;
    c_effect : Effect.t;
    c_pre    : precondition list;
    c_post   : postcondition option }

type transp = Transparent | Opaque

