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

let grab_infos = 
  let r_loc = Str.regexp "File \"\\(.+\\)\", line \\([0-9]+\\), characters \\([0-9]+\\)-\\([0-9]+\\)" in
  fun s -> 
    if Str.string_match r_loc s 0 then 
      let source = Filename.concat (Sys.getcwd ()) (Str.matched_group 1 s) in
      Some({file=source;
            line=(Str.matched_group 2 s);
            sp=(Str.matched_group 3 s);
            ep=(Str.matched_group 4 s)})
    else None

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "int"
  | PTbool -> fprintf fmt "bool"
  | PTunit -> fprintf fmt "void"
  | PTreal -> fprintf fmt "float"
  | PTexternal ([v], id) when id == farray -> 
      fprintf fmt "@[(array %a)@]" print_pure_type v
  | PTexternal([],id) -> Ident.print fmt id
  | PTexternal(l,id) -> 
      fprintf fmt "@[((%a) %a)@]"
      Ident.print id
      (print_list space print_pure_type) l
  | PTvar { type_val = Some t} -> 
      fprintf fmt "%a" print_pure_type t      
  | PTvar v ->
      fprintf fmt "A%d" v.tag

let print_binder = Coq.print_binder_v8
let print_binder_type = Coq.print_binder_type_v8
let print_term = Coq.print_term_v8

let infix_relation id =
  if id == t_lt_int then "<" 
  else if id == t_le_int then "<="
  else if id == t_gt_int then ">"
  else if id == t_ge_int then ">="
  else if id == t_eq_int then "="
  else if id == t_neq_int then "<>"
  else assert false

let pprefix_id id =
  if id == t_lt_real then "Rlt"
  else if id == t_le_real then "Rle"
  else if id == t_gt_real then "Rgt" 
  else if id == t_ge_real then "Rge"
  else assert false

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
    | Por (a, b) -> fprintf fmt "@[%a \\/@ %a@]" print2 a print1 b
    | p -> print2 fmt p
  and print2 fmt = function
    | Pand (_, _, a, b) | Forallb (_, a, b) -> 
        fprintf fmt "@[%a /\\@ %a@]" print3 a print2 b
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
	(pprefix_id id) print_term a print_term b
    | Papp (id, l, _) ->
	fprintf fmt "@[(@[%a %a@])@]" Ident.print id
	  (print_list space print_term) l
    | Pnot p -> 
	fprintf fmt "~%a" print3 p
    | Forall (_,id,n,t,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = subst_in_predicate (subst_onev n id') p in
	fprintf fmt "(@[forall (%s:%a),@ %a@])" (Ident.string id')
	  print_pure_type t print0 p'
    | Exists (id,n,t,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = subst_in_predicate (subst_onev n id') p in
	fprintf fmt "(@[exists %s:%a,@ %a@])" (Ident.string id')
	  print_pure_type t print0 p'
    | Pfpi _ ->
	failwith "fpi not supported with Coq V8"
    | Pnamed (n, p) ->
	(match (grab_infos n) with
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

let rec print_cc_type_v8 fmt = function
  | TTpure pt -> 
      print_pure_type fmt pt
  | TTarray v -> 
      fprintf fmt "(@[array@ %a@])" print_cc_type_v8 v
  | TTlambda (b, t) ->
      fprintf fmt "(@[fun %a =>@ %a@])" print_binder b print_cc_type_v8 t
  | TTarrow (b, t) -> 
      fprintf fmt "@[forall %a,@ %a@]" print_binder b print_cc_type_v8 t
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
