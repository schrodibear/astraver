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

(* $Id: WhyFloat.v,v 1.3 2002-12-04 10:29:50 filliatr Exp $ *)

Require Why.
Require Export RealsB.

Parameter R_lt_ge_bool : 
 (x,y:R) { b:bool | if b then ``x < y`` else ``x >= y`` }.
Parameter R_le_gt_bool : 
 (x,y:R) { b:bool | if b then ``x <= y`` else ``x > y`` }.
Parameter R_gt_le_bool : 
 (x,y:R) { b:bool | if b then ``x > y`` else ``x <= y`` }.
Parameter R_ge_lt_bool : 
 (x,y:R) { b:bool | if b then ``x >= y`` else ``x < y`` }.
Parameter R_eq_bool : 
 (x,y:R) { b:bool | if b then ``x == y`` else ``x <> y`` }.
Parameter R_noteq_bool : 
 (x,y:R) { b:bool | if b then ``x <> y`` else ``x == y`` }.
