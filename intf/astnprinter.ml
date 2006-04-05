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
open Astprinter

let print_term fmt t = 
  let rec print0 fmt = function
    | Tapp (id, [a;b], _) when is_relation id ->
	fprintf fmt "(@[<hov 2>%s@ %a@ %a@])" (Coq.prefix_id id)
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
	fprintf fmt "(@[int_div %a@ %a@])" print2 a print3 b
    | Tapp (id, [a;b], _) when id == t_mod_int ->
	fprintf fmt "(@[int_mod %a@ %a@])" print2 a print3 b
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
    | Tapp (id, [t], _) when id == t_neg_int ->
	fprintf fmt "(Zopp %a)" print3 t
    | Tapp (id, [_;_], _) as t when is_relation id || is_int_arith_binop id ->
	fprintf fmt "@[(%a)@]" print0 t
    | Tapp (id, [a; b; c], _) when id == if_then_else -> 
	fprintf fmt "(@[if_then_else %a@ %a@ %a@])" print0 a print0 b print0 c
    | Tapp (id, tl, _) when id == t_zwf_zero -> 
	fprintf fmt "(@[Zwf 0 %a@])" print_terms tl
    | Tapp (id, tl, _) when is_relation id || is_arith id -> 
	fprintf fmt "(@[%s %a@])" (Coq.prefix_id id) print_terms tl
    | Tapp (id, tl, _) -> 
	fprintf fmt "(@[%s %a@])" (Ident.string id) print_terms tl
  and print_terms fmt tl =
    print_list space print3 fmt tl
  in
  print3 fmt t

let print_predicate fmt p =
  let rec print0 fmt = function
    | Pif (a, b, c) -> 
	fprintf fmt "(@[if %a@ then %a@ else %a@])"
	  print_term a print0 b print0 c
    | Pimplies (_, a, b) -> 
	fprintf fmt "(@[%a =>@ %a@])" print1 a print0 b
    | Piff (a, b) -> 
	fprintf fmt "(@[%a <->@ %a@])" print1 a print0 b
    | p -> print1 fmt p
  and print1 fmt = function
    | Por (a, b) -> fprintf fmt "@[%a or@ %a@]" print2 a print1 b
    | p -> print2 fmt p
  and print2 fmt = function
    | Pand (_, _, a, b) | Forallb (_, a, b) -> 
        fprintf fmt "@[%a and@ %a@]" print3 a print2 b
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
	  print_term a (Coq.infix_relation id) print_term b
    | Papp (id, [a;b], _) when id == t_eq_real || id == t_eq ->
	fprintf fmt "(@[%a = %a@])" print_term a print_term b
    | Papp (id, [a;b], _) when id == t_neq_real || id == t_neq ->
	fprintf fmt "(@[%a <> %a@])" print_term a print_term b
    | Papp (id, [a;b], _) when is_real_comparison id ->
	fprintf fmt "(@[%s %a %a@])" 
	(Coq.pprefix_id id) print_term a print_term b
    | Papp (id, l, _) ->
	fprintf fmt "@[(@[%a %a@])@]" Ident.print id
	  (print_list space print_term) l
    | Pnot p -> 
	fprintf fmt "not %a" print3 p
    | Forall (_,id,n,t,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = subst_in_predicate (subst_onev n id') p in
	fprintf fmt "(@[forall %s:%a.@ %a@])" (Ident.string id')
	  print_pure_type t print0 p'
    | Exists (id,n,t,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = subst_in_predicate (subst_onev n id') p in
	fprintf fmt "(@[exists %s:%a,@ %a@])" (Ident.string id')
	  print_pure_type t print0 p'
    | Pfpi _ ->
	failwith "fpi not supported"
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
