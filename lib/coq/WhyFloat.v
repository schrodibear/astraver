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

(* $Id: WhyFloat.v,v 1.7 2003-09-22 13:11:59 filliatr Exp $ *)

Require Why.
Require Export Rbase.

Open Scope R_scope.

Parameter R_lt_ge_bool : 
 forall x y:R, { b:bool | if b then x < y else x >= y }.
Parameter R_le_gt_bool : 
 forall x y:R, { b:bool | if b then x <= y else x > y }.
Parameter R_gt_le_bool : 
 forall x y:R, { b:bool | if b then x > y else x <= y }.
Parameter R_ge_lt_bool : 
 forall x y:R, { b:bool | if b then x >= y else x < y }.
Parameter R_eq_bool : 
 forall x y:R, { b:bool | if b then x = y else x <> y }.
Parameter R_noteq_bool : 
 forall x y:R, { b:bool | if b then x <> y else x = y }.

(* no validation for programs using floats
Parameter why_any_float : (_: unit)(sig_1 R [result: R](True)).
*)