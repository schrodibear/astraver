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

(*i $Id: harvey.ml,v 1.9 2003-05-12 14:13:38 filliatr Exp $ i*)

(*s Harvey's output *)

open Ident
open Misc
open Error
open Logic
open Vcg
open Format

let oblig = Queue.create ()

let reset () = Queue.clear oblig

let push_obligations = List.iter (fun o -> Queue.add o oblig)

(*s Pretty print *)

let uncapitalize fmt id = 
  fprintf fmt "%s" (String.uncapitalize (Ident.string id))

let prefix id =
  if id == t_lt then "arith_less"
  else if id == t_le then "arith_leq"
  else if id == t_gt then "arith_gr"
  else if id == t_ge then "arith_greq"
  (* int cmp *)
  else if id == t_lt_int then "arith_less"
  else if id == t_le_int then "arith_leq"
  else if id == t_gt_int then "arith_gr"
  else if id == t_ge_int then "arith_greq"
  (* int ops *)
  else if id == t_add_int then "arith_add"
  else if id == t_sub_int then "arith_minus"
  else if id == t_mul_int then "arith_times"
  else if id == t_div_int then "arith_div"
  else if id == t_mod_int then "arith_mod"
  else if id == t_neg_int then "arith_opp"
  (* float ops *)
  else assert false

let rec print_term fmt = function
  | Tvar id -> 
      fprintf fmt "%a" uncapitalize id
  | Tconst (ConstInt n) -> 
      fprintf fmt "%d" n
  | Tconst (ConstBool b) -> 
      fprintf fmt "%b" b
  | Tconst ConstUnit -> 
      fprintf fmt "tt" 
  | Tconst (ConstFloat _) ->
      Report.raise_unlocated (AnyMessage "haRVey does not support floats")
  | Tderef _ -> 
      assert false
  | Tapp (id, [a; b; c]) when id == if_then_else -> 
      fprintf fmt "@[(ite@ %a@ %a@ %a)@]" print_term a print_term b
	print_term c
  | Tapp (id, tl) when is_relation id || is_arith id ->
      fprintf fmt "@[(%s %a)@]" (prefix id) print_terms tl
  | Tapp (id, tl) ->
      fprintf fmt "@[(%a@ %a)@]" 
	uncapitalize id (print_list space print_term) tl

and print_terms fmt tl = 
  print_list space print_term fmt tl

let rec print_predicate fmt = function
  | Ptrue ->
      fprintf fmt "true"
  | Pvar id when id == default_post ->
      fprintf fmt "true"
  | Pfalse ->
      fprintf fmt "false"
  | Pvar id -> 
      fprintf fmt "%a" uncapitalize id
  | Papp (id, [a; b]) when is_eq id ->
      fprintf fmt "@[(= %a@ %a)@]" print_term a print_term b
  | Papp (id, [a; b]) when is_neq id ->
      fprintf fmt "@[(not (= %a@ %a))@]" print_term a print_term b
  | Papp (id, tl) when is_relation id || is_arith id ->
      fprintf fmt "@[(%s %a)@]" (prefix id) print_terms tl
  | Papp (id, [a;b]) when id == t_zwf_zero ->
      fprintf fmt "@[(and (arith_leq 0 %a)@ (arith_less %a %a))@]" 
	print_term b print_term a print_term b
  | Papp (id, tl) -> 
      fprintf fmt "@[(%a@ %a)@]" uncapitalize id print_terms tl
  | Pimplies (_, a, b) ->
      fprintf fmt "@[(->@ %a@ %a)@]" print_predicate a print_predicate b
  | Pif (a, b, c) ->
      fprintf fmt "@[(ite@ %a@ %a@ %a)@]" print_term a print_predicate b
	print_predicate c
  | Pand (_, a, b) | Forallb (_, _, _, _, a, b) ->
      fprintf fmt "@[(and@ %a@ %a)@]" print_predicate a print_predicate b
  | Por (a, b) ->
      fprintf fmt "@[(or@ %a@ %a)@]" print_predicate a print_predicate b
  | Pnot a ->
      fprintf fmt "@[(not@ %a)@]" print_predicate a
  | Forall (_,id,n,_,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(FORALL (%a)@ %a)@]" Ident.print id' print_predicate p'
  | Exists (id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(EXISTS (%a)@ %a)@]" Ident.print id' print_predicate p'

let output_sequent fmt (ctx, c) = match ctx with
  | [] -> 
      fprintf fmt "@[%a@]" print_predicate c
  | [p] -> 
      fprintf fmt "@[<hov 2>(->@ @[%a@]@ %a)@]" 
	print_predicate p print_predicate c
  | ctx -> 
      fprintf fmt "@[<hov 2>(->@ @[<hov 2>(and@ %a)@]@ %a)@]"
	(print_list space print_predicate) ctx print_predicate c

(*s First-order checks *)

(*
let rec is_first_order = function
  | Pvar _
  | Papp _
  | Ptrue
  | Pfalse -> true
  | Pimplies (a, b) -> is_first_order a && is_first_order b
  | Pif (_, a, b) -> is_first_order a && is_first_order b
  | Pand (a, b) | Por (a, b) -> is_first_order a && is_first_order b
  | Pnot a -> is_first_order a 
  | Forall _
  | Exists _ -> false
*)

let rec filter_context = function
  | [] -> []
  | Svar (id, _) :: ctx -> filter_context ctx
  | Spred (_, p) :: ctx -> p :: filter_context ctx

exception NotFirstOrder

let rec prepare_conclusion = function
  | Forall (_, _, _, _, p) -> prepare_conclusion p
  | p -> p

let prepare_sequent (ctx, c) = 
  filter_context ctx, prepare_conclusion c

let output_obligation f (loc, o, s) = 
  try
    let s = prepare_sequent s in
    let fname = f ^ "_" ^ o ^ ".rv" in
    let cout = open_out fname in
    let fmt = formatter_of_out_channel cout in
    fprintf fmt "@[;; %a@]@\n" Loc.report_obligation loc;
    output_sequent fmt s;
    pp_print_flush fmt ();
    close_out cout
  with NotFirstOrder ->
    unlocated_wprintf "obligation %s is not first-order@\n" o

let output_file f = Queue.iter (output_obligation f) oblig


