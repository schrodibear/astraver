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

(*i $Id: harvey.ml,v 1.22 2004-12-01 17:10:03 filliatr Exp $ i*)

(*s Harvey's output *)

open Ident
open Misc
open Error
open Logic
open Vcg
open Format
open Pp

let oblig = Queue.create ()
let axiom = Queue.create ()

let reset () = Queue.clear oblig; Queue.clear axiom

let push_obligations = List.iter (fun o -> Queue.add o oblig)

let push_axiom id p = Queue.add (id, p) axiom

let push_predicate id p = assert false (*TODO*)

(*s Pretty print *)

let prefix id =
  if id == t_lt then assert false
  else if id == t_le then assert false
  else if id == t_gt then assert false
  else if id == t_ge then assert false
  (* int cmp *)
  else if id == t_lt_int then "<"
  else if id == t_le_int then "<="
  else if id == t_gt_int then ">"
  else if id == t_ge_int then ">="
  (* int ops *)
  else if id == t_add_int then "+"
  else if id == t_sub_int then "-"
  else if id == t_mul_int then "*"
  else if id == t_div_int then "int_div"
  else if id == t_mod_int then "int_mod"
  else if id == t_neg_int then "-"
  (* real ops *)
  else if id == t_add_real 
       || id == t_sub_real 
       || id == t_mul_real 
       || id == t_div_real 
       || id == t_neg_real 
       || id == t_sqrt_real 
       || id == t_real_of_int 
  then
    Report.raise_unlocated (AnyMessage "haRVey does not support reals")
  else assert false

let rec print_term fmt = function
  | Tvar id -> 
      fprintf fmt "%a" Ident.print id
  | Tconst (ConstInt n) -> 
      fprintf fmt "%d" n
  | Tconst (ConstBool b) -> 
      fprintf fmt "%b" b
  | Tconst ConstUnit -> 
      fprintf fmt "tt" 
  | Tconst (ConstFloat _) ->
      Report.raise_unlocated (AnyMessage "haRVey does not support reals")
  | Tderef _ -> 
      assert false
  | Tapp (id, [a; b; c], _) when id == if_then_else -> 
      fprintf fmt "@[(ite@ %a@ %a@ %a)@]" print_term a print_term b
	print_term c
  | Tapp (id, tl, _) when is_relation id || is_arith id ->
      fprintf fmt "@[(%s %a)@]" (prefix id) print_terms tl
  | Tapp (id, tl, _) ->
      fprintf fmt "@[(%a@ %a)@]" 
	Ident.print id (print_list space print_term) tl

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
      fprintf fmt "%a" Ident.print id
  | Papp (id, [a; b], _) when is_eq id ->
      fprintf fmt "@[(= %a@ %a)@]" print_term a print_term b
  | Papp (id, [a; b], _) when is_neq id ->
      fprintf fmt "@[(not (= %a@ %a))@]" print_term a print_term b
  | Papp (id, tl, _) when is_relation id || is_arith id ->
      fprintf fmt "@[(%s %a)@]" (prefix id) print_terms tl
  | Papp (id, [a;b], _) when id == t_zwf_zero ->
      fprintf fmt "@[(and (<= 0 %a)@ (< %a %a))@]" 
	print_term b print_term a print_term b
  | Papp (id, tl, _) -> 
      fprintf fmt "@[(%a@ %a)@]" Ident.print id print_terms tl
  | Pimplies (_, a, b) ->
      fprintf fmt "@[(->@ %a@ %a)@]" print_predicate a print_predicate b
  | Pif (a, b, c) ->
      fprintf fmt "@[(ite@ %a@ %a@ %a)@]" print_term a print_predicate b
	print_predicate c
  | Pand (_, a, b) | Forallb (_, a, b) ->
      fprintf fmt "@[(and@ %a@ %a)@]" print_predicate a print_predicate b
  | Por (a, b) ->
      fprintf fmt "@[(or@ %a@ %a)@]" print_predicate a print_predicate b
  | Piff (a, b) ->
      fprintf fmt "@[(<->@ %a@ %a)@]" print_predicate a print_predicate b
  | Pnot a ->
      fprintf fmt "@[(not@ %a)@]" print_predicate a
  | Forall (_,id,n,_,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(forall %a@ %a)@]" Ident.print id' print_predicate p'
  | Exists (id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(exists %a@ %a)@]" Ident.print id' print_predicate p'
  | Pfpi _ ->
      failwith "fpi not supported with haRVey"
  | Pnamed (_, p) -> (* TODO: print name *)
      print_predicate fmt p

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

let prepare_sequent (ctx, c) = filter_context ctx, c

let output_axioms f =
  let fname = f ^ "_axioms.rv" in
  let cout = open_out fname in
  let fmt = formatter_of_out_channel cout in
  fprintf fmt "(@[";
  Queue.iter 
    (fun (id, p) -> 
       fprintf fmt ";; why axiom %s@\n(@[%a@])@\n" 
	 id print_predicate p.Env.scheme_type)
    axiom;
  fprintf fmt "@])@\n";
  pp_print_flush fmt ();
  close_out cout

let output_obligation f (loc, o, s) = 
  try
    let s = prepare_sequent s in
    let fname = f ^ "_" ^ o ^ ".rv" in
    let cout = open_out fname in
    let fmt = formatter_of_out_channel cout in
    fprintf fmt "@[";
    if not Options.no_harvey_prelude then fprintf fmt "()@\n";
    fprintf fmt ";; %a@]@\n" Loc.report_obligation loc;
    output_sequent fmt s;
    pp_print_flush fmt ();
    close_out cout
  with NotFirstOrder ->
    unlocated_wprintf "obligation %s is not first-order@\n" o

let output_file f = 
  output_axioms f;
  Queue.iter (output_obligation f) oblig


