(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: WhyFloat.v,v 1.1 2002-07-19 11:23:19 filliatr Exp $ *)

Require Why.
Require Export Reals.

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
