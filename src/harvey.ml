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

(*i $Id: harvey.ml,v 1.25 2005-05-25 13:03:52 filliatr Exp $ i*)

(*s Harvey's output *)

open Ident
open Misc
open Error
open Logic
open Vcg
open Format
open Pp

type elem = 
  | Axiom of string * predicate Env.scheme
  | Predicate of string * predicate_def Env.scheme

let theory = Queue.create ()
let oblig = Queue.create ()

let reset () = Queue.clear theory; Queue.clear oblig

let push_obligations = List.iter (fun o -> Queue.add o oblig)

let push_axiom id p = Queue.add (Axiom (id, p)) theory

let push_predicate id p = Queue.add (Predicate (id, p)) theory

let defpred = Hashtbl.create 97

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
  else if id == t_neg_int then assert false
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
  | Tapp (id, [a], _) when id == t_neg_int ->
      fprintf fmt "@[(- 0 %a)@]" print_term a
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

let print_axiom fmt id p =
  fprintf fmt "@[;; Why axiom %s@]@\n" id;
  let p = p.Env.scheme_type in
  fprintf fmt " @[<hov 2>%a@]" print_predicate p;
  fprintf fmt "@]@\n@\n" 

let print_predicate_def fmt id p =
  let (bl,p) = p.Env.scheme_type in
  fprintf fmt "@[(forall %a (<-> (%s %a)@ @[%a@]))@]@\n@\n" 
    (print_list space (fun fmt (x,_) -> Ident.print fmt x)) bl id
    (print_list space (fun fmt (x,_) -> Ident.print fmt x)) bl 
    print_predicate p;
  Hashtbl.add defpred (Ident.create id) ()

let print_elem fmt = function
  | Axiom (id, p) -> print_axiom fmt id p
  | Predicate (id, p) -> print_predicate_def fmt id p

let output_theory fmt =
  fprintf fmt "(@\n@[";
  Queue.iter (print_elem fmt) theory;
  fprintf fmt "@]@\n) ;; END THEORY@\n"

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

let output_obligation fmt (loc, o, s) = 
  try
    let s = prepare_sequent s in
    fprintf fmt "@[;; %a@]@\n" Loc.report_obligation loc;
    output_sequent fmt s
  with NotFirstOrder ->
    unlocated_wprintf "obligation %s is not first-order@\n" o

let output_file f = 
  let fname = f ^ "_why.rv" in
  let cout = open_out fname in
  let fmt = formatter_of_out_channel cout in
  if Options.no_harvey_prelude then fprintf fmt "()@\n" else output_theory fmt;
  Queue.iter (output_obligation fmt) oblig;
  pp_print_flush fmt ();
  close_out cout

