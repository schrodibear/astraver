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
open Pp

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "int"
  | PTbool -> fprintf fmt "bool"
  | PTunit -> fprintf fmt "void"
  | PTreal -> fprintf fmt "float"
  | PTexternal ([v], id) when id == farray -> 
      fprintf fmt "(array %a)" print_pure_type v
  | PTexternal([],id) -> Ident.print fmt id
  | PTexternal(l,id) -> 
      fprintf fmt "((%a) %a)"
      Ident.print id
      (print_list space print_pure_type) l
  | PTvar { type_val = Some t} -> 
      fprintf fmt "%a" print_pure_type t      
  | PTvar v ->
      fprintf fmt "A%d" v.tag

let print_predicate = Coq.print_predicate_v8
let print_binder = Coq.print_binder_v8
let print_binder_type = Coq.print_binder_type_v8
let print_term = Coq.print_term_v8

let rec print_cc_type_v8 fmt = function
  | TTpure pt -> 
      print_pure_type fmt pt
  | TTarray v -> 
      fprintf fmt "(@[array@ %a@])" print_cc_type_v8 v
  | TTlambda (b, t) ->
      fprintf fmt "(@[fun %a =>@ %a@])" print_binder b print_cc_type_v8 t
  | TTarrow (b, t) -> 
      fprintf fmt "forall %a,@ %a" print_binder b print_cc_type_v8 t
  | TTtuple ([_,CC_var_binder t], None) -> 
      print_cc_type_v8 fmt t
  | TTtuple (bl, None) ->
      fprintf fmt "(@[tuple_%d@ %a@])" (List.length bl) 
	(print_list space print_binder_type) bl
  | TTtuple (bl, Some q) -> 
      fprintf fmt "(@[sig_%d@ %a@ (@[fun %a =>@ (%a)@])@])" (List.length bl)
	(print_list space print_binder_type) bl 
	(print_list nothing 
	   (fun fmt b -> fprintf fmt "%a@ " print_binder b)) bl
	print_cc_type_v8 q
  | TTpred p ->
      print_predicate fmt p
  | TTapp (tt, l) ->
      fprintf fmt "(@[%a@ %a@])" print_cc_type_v8 tt
	(print_list space print_cc_type_v8) l
  | TTterm t ->
      print_term fmt t
  | TTSet ->
      fprintf fmt "Set"

let print_cc_type = print_cc_type_v8
