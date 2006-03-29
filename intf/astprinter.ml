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

open Logic
open Cc
open Ident
open Format
open Misc
open Pp
open Tags

let prefix_id id =
  (* int or real cmp *)
  if id == t_lt_int or id == t_lt_real then "<" 
  else if id == t_le_int or id == t_le_real then "<="
  else if id == t_gt_int or id == t_gt_real then ">"
  else if id == t_ge_int or id == t_ge_real then ">="
  else if id == t_eq_int or id == t_eq_real then "="
  else if id == t_neq_int or id == t_neq_real then "!="
  (* bool cmp *)
  else if id == t_eq_bool then "="
  else if id == t_neq_bool then "!="
  (* unit cmp *)
  else if id == t_eq_unit then "U_eq_bool"
  else if id == t_neq_unit then "U_noteq_bool"
  (* int or real ops *)
  else if id == t_add_int or id == t_add_real then "+"
  else if id == t_sub_int or id == t_sub_real then "-"
  else if id == t_mul_int or id == t_mul_real then "*"
  else if id == t_div_int or id == t_div_real then "/"
  else if id == t_mod_int                     then "%"
  else if id == t_neg_int or id == t_neg_real then "-"
  (* real ops *)
  else if id == t_sqrt_real then "sqrt"
  else if id == t_real_of_int then "IZR"
  else if id == t_int_of_real then "int_of_real"
  else assert false

let infix_relation id =
       if id == t_neq_int then "!=" 
  else Coq.infix_relation id

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "int"
  | PTbool -> fprintf fmt "bool"
  | PTunit -> fprintf fmt "unit"
  | PTreal -> fprintf fmt "real"
  | PTexternal ([v], id) when id == farray -> 
      fprintf fmt "@[%a array@]" print_pure_type v
  | PTexternal([],id) -> Ident.print fmt id
  | PTexternal([l],id) -> 
      fprintf fmt "@[%a %a@]"
	print_pure_type l
	Ident.print id
  | PTexternal(l,id) -> 
      fprintf fmt "@[(%a) %a@]"
	(print_list comma print_pure_type) l
	Ident.print id
  | PTvar { type_val = Some t} -> 
      fprintf fmt "%a" print_pure_type t      
  | PTvar v ->
      fprintf fmt "A%d" v.tag

let print_binder = Coq.print_binder_v8
let print_binder_type = Coq.print_binder_type_v8

let rec print_cc_type fmt = function
  | TTpure pt -> 
      print_pure_type fmt pt
  | t -> Coq.print_cc_type_v8 fmt t
