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
  | PTunit -> fprintf fmt "void"
  | PTreal -> fprintf fmt "float"
  | PTexternal ([v], id) when id == farray -> 
      fprintf fmt "@[(array %a)@]" print_pure_type v
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

let print_term fmt t = 
  let rec print0 fmt = function
    | Tapp (id, [a;b], _) when is_relation id ->
	fprintf fmt "(@[<hov 2>%s@ %a@ %a@])" (prefix_id id)
	print3 a print3 b
    | t -> 
	print1 fmt t
  and print1 fmt = function
    | Tapp (id, [a;b], _) when id == t_add_int ->
	fprintf fmt "%a +@ %a" print1 a print2 b
    | Tapp (id, [a;b], _) when id == t_sub_int ->
	fprintf fmt "%a -@ %a" print1 a print2 b
    | t ->
	print2 fmt t
  and print2 fmt = function
    | Tapp (id, [a;b], _) when id == t_mul_int ->
	fprintf fmt "%a *@ %a" print2 a print3 b
    | Tapp (id, [a;b], _) when id == t_div_int ->
	fprintf fmt "@[%a@ / %a@]" print2 a print3 b
    | Tapp (id, [a;b], _) when id == t_mod_int ->
	fprintf fmt "(@[%a@ %% %a@])" print2 a print3 b
    | t ->
	print3 fmt t
  and print3 fmt = function
    | Tconst (ConstInt n) -> 
	fprintf fmt "%s" n
    | Tconst (ConstBool b) -> 
	fprintf fmt "%b" b
    | Tconst ConstUnit -> 
	fprintf fmt "tt" 
    | Tconst (ConstFloat (i,f,e)) -> 
	let f = if f = "0" then "" else f in
	let e = (if e = "" then 0 else int_of_string e) - String.length f in
	if e = 0 then
	  fprintf fmt "(%s%s)%%R" i f
	else if e > 0 then
	  fprintf fmt "(%s%s * 1%s)%%R" i f (String.make e '0')
	else
	  fprintf fmt "(%s%s / 1%s)%%R" i f (String.make (-e) '0')
    | Tvar id when id == implicit ->
	fprintf fmt "?"
    | Tvar id when id == t_zwf_zero ->
	fprintf fmt "(Zwf Z0)"
    | Tvar id | Tapp (id, [], _) -> 
	Ident.print fmt id
    | Tderef _ ->
	assert false
    | Tapp (id, _, _) as t when (Ident.string id = "acc") ->
	print_fct_acc fmt t
    | Tapp (id, _, _) as t when (Ident.string id = "shift") ->
	print_fct_shift fmt t
    | Tapp (id, [t], _) when id == t_neg_int ->
	fprintf fmt "(- %a)" print3 t
    | Tapp (id, [_;_], _) as t when is_relation id || is_int_arith_binop id ->
	fprintf fmt "@[(%a)@]" print0 t
    | Tapp (id, [a; b; c], _) when id == if_then_else -> 
	fprintf fmt "(@[if_then_else %a@ %a@ %a@])" print0 a print0 b print0 c
    | Tapp (id, [a;b], _) when id == t_zwf_zero -> 
	fprintf fmt "(@[0 <= %a && %a < %a@])" print0 b print0 a print0 b
    | Tapp (id, tl, _) when is_arith id -> 
	fprintf fmt "(@[%s %a@])" (prefix_id id) print_terms tl
    | Tapp (id, tl, _) -> 
	fprintf fmt "(@[%s %a@])" (Ident.string id) print_terms tl
  and print_terms fmt tl =
    print_list space print3 fmt tl
  and is_shift = function 
    | Tapp (id, _, _) when (Ident.string id = "shift") -> true
    | _ -> false
  and print_fct_acc fmt = function
	| Tapp (id, [m; term], _) -> 
	    if (is_shift term) 
	    then fprintf fmt "%a{%a}" print_fct_acc_shift term print3 m
	    else fprintf fmt "%a{%a}" print3 term print3 m
	| t -> print3 fmt t
  and print_fct_acc_shift fmt = function 
    | Tapp (id, [p; offset], _) -> fprintf fmt "%a[%a]" print3 p print3 offset;
    | t -> print3 fmt t
  and print_fct_shift fmt = function
	 | Tapp (id, [p; offset], _) -> 
	     fprintf fmt "%a + %a" print3 p print3 offset
	 | t -> print3 fmt t
  in
  print3 fmt t

let print_predicate fmt p =
  let rec print0 fmt = function
    | Pif (a, b, c) -> 
	fprintf fmt "(@[if %a@ then %a@ else %a@])"
	  print_term a print0 b print0 c
    | Pimplies (_, a, b) -> 
	fprintf fmt "(@[%a ->@ %a@])" print1 a print0 b
    | Piff (a, b) -> 
	fprintf fmt "(@[%a <->@ %a@])" print1 a print0 b
    | p -> print1 fmt p
  and print1 fmt = function
    | Por (a, b) -> fprintf fmt "@[%a ||@ %a@]" print2 a print1 b
    | p -> print2 fmt p
  and print2 fmt = function
    | Pand (_, _, a, b) | Forallb (_, a, b) -> 
        fprintf fmt "@[%a &&@ %a@]" print3 a print2 b
    | p -> print3 fmt p
  and print3 fmt = function
    | Ptrue -> 
	fprintf fmt "True"
    | Pvar id when id == Ident.default_post ->
	fprintf fmt "True"
    | Pfalse -> 
	fprintf fmt "False"
    | Pvar id -> 
	Ident.print fmt id
    | Papp (id, [t], _) when id == well_founded ->
	fprintf fmt "@[(well_founded %a)@]" print_term t
    | Papp (id, [a;b], _) when id == t_zwf_zero ->
	fprintf fmt "(Zwf 0 %a %a)" print_term a print_term b
    | Papp (id, [a;b], _) when is_int_comparison id ->
	fprintf fmt "@[%a %s@ %a@]" 
	  print_term a (infix_relation id) print_term b
    | Papp (id, [a;b], _) when id == t_eq_real ->
	fprintf fmt "(@[eq %a %a@])" print_term a print_term b
    | Papp (id, [a;b], _) when id == t_neq_real ->
	fprintf fmt "~(@[eq %a %a@])" print_term a print_term b
    | Papp (id, [a;b], _) when is_eq id ->
	fprintf fmt "@[%a = %a@]" print_term a print_term b
    | Papp (id, [a;b], _) when is_neq id -> 
	fprintf fmt "@[~(%a = %a)@]" print_term a print_term b
    | Papp (id, [a;b], _) when is_real_comparison id ->
	fprintf fmt "(@[%s %a %a@])" 
	(Coq.pprefix_id id) print_term a print_term b
    | Papp (id, l, _) ->
	fprintf fmt "@[(@[%a %a@])@]" Ident.print id
	  (print_list space print_term) l
    | Pnot p -> 
	fprintf fmt "~%a" print3 p
    | Forall (_,id,n,t,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = subst_in_predicate (subst_onev n id') p in
	fprintf fmt "@[\\forall %s:%a;@ %a@]" (Ident.string id')
	  print_pure_type t print0 p'
    | Exists (id,n,t,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = subst_in_predicate (subst_onev n id') p in
	fprintf fmt "(@[exists %s:%a,@ %a@])" (Ident.string id')
	  print_pure_type t print0 p'
    | Pfpi _ ->
	failwith "fpi not supported with Coq V8"
    | Pnamed (n, p) ->
	(match (Tools.grab_infos n) with
	   | None -> fprintf fmt "@[%a@]" print3 p
	   | Some l ->
	       let n = new_tag l in
	       pp_open_tag fmt n;
	       fprintf fmt "@[%a@]" print3 p;
	       pp_close_tag fmt ()
	)
    | (Por _ | Piff _ | Pand _ | Pif _ | Pimplies _ | Forallb _) as p -> 
	fprintf fmt "@[(%a)@]" print0 p
  in
  print0 fmt p

let rec print_cc_type fmt = function
  | TTpure pt -> 
      print_pure_type fmt pt
  | t -> Coq.print_cc_type_v8 fmt t
