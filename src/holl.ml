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

(*i $Id: holl.ml,v 1.3 2003-01-09 16:50:21 filliatr Exp $ i*)

(*s HOL Light output *)

open Ident
open Misc
open Error
open Logic
open Vcg
open Format
open Cc

type elem = 
  | Parameter of string * cc_type
  | Obligation of obligation

let elem_q = Queue.create ()

let reset () = Queue.clear elem_q

let push_parameter id v = Queue.add (Parameter (id, v)) elem_q

let push_obligations = List.iter (fun o -> Queue.add (Obligation o) elem_q)

(*s Pretty print *)

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "int"
  | PTbool -> fprintf fmt "bool"
  | PTunit -> fprintf fmt "one"
  | PTfloat -> fprintf fmt "real"
  | PTarray v -> fprintf fmt "list(%a)" print_pure_type v
  | PTexternal id -> Ident.print fmt id

let rec print_term fmt = function
  | Tvar id -> 
      Ident.print fmt id
  | Tconst (ConstInt n) -> 
      fprintf fmt "%d" n
  | Tconst (ConstBool true) -> 
      fprintf fmt "T" 
  | Tconst (ConstBool false) -> 
      fprintf fmt "F" 
  | Tconst ConstUnit -> 
      fprintf fmt "one" 
  | Tconst (ConstFloat f) ->
      fprintf fmt "%s" f
  | Tderef _ -> 
      assert false
(**
  | Tapp (id, tl) when is_relation id || is_arith id ->
      fprintf fmt "@[(%s %a)@]" ( id) print_terms tl
**)
  | Tapp (id, tl) ->
      fprintf fmt "@[(%a@ %a)@]" 
	Ident.print id (print_list space print_term) tl

and print_terms fmt tl = 
  print_list space print_term fmt tl

let rec print_predicate fmt = function
  | Ptrue ->
      fprintf fmt "T"
  | Pfalse ->
      fprintf fmt "F"
  | Pvar id when id == default_post ->
      fprintf fmt "F"
  | Pvar id -> 
      fprintf fmt "%a" Ident.print id
  | Papp (id, [a; b]) when is_eq id ->
      fprintf fmt "@[(%a =@ %a)@]" print_term a print_term b
  | Papp (id, [a; b]) when is_neq id ->
      fprintf fmt "@[~(%a =@ %a))@]" print_term a print_term b
(**
  | Papp (id, tl) when is_relation id || is_arith id ->
      fprintf fmt "@[(%s %a)@]" (prefix id) print_terms tl
**)
  | Papp (id, [a;b]) when id == t_zwf_zero ->
      fprintf fmt "@[(and (arith_leq 0 %a)@ (arith_less %a %a))@]" 
	print_term b print_term a print_term b
  | Papp (id, tl) -> 
      fprintf fmt "@[(%a@ %a)@]" Ident.print id print_terms tl
  | Pimplies (a, b) ->
      fprintf fmt "(@[%a ==>@ %a@])" print_predicate a print_predicate b
  | Pif (a, b, c) ->
      fprintf fmt "(@[if %a@ then %a@ else %a@])" 
	print_term a print_predicate b print_predicate c
  | Pand (a, b) ->
      fprintf fmt "@[(%a /\\@ %a)@]" print_predicate a print_predicate b
  | Por (a, b) ->
      fprintf fmt "@[(%a \\/@ %a)@]" print_predicate a print_predicate b
  | Pnot a ->
      fprintf fmt "@[(~%a)@]" print_predicate a
  | Forall (id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "(@[!%s:%a.@ %a@])" (Ident.string id')
	print_pure_type t print_predicate p'
  | Exists (id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "(@[?%s:%a.@ %a@])" (Ident.string id')
	print_pure_type t print_predicate p'

let rec print_cc_type fmt = function
  | TTpure pt -> 
      print_pure_type fmt pt
  | _ ->
      fprintf fmt "<type>"

let print_sequent fmt (hyps,concl) =
  let rec print_seq fmt = function
    | [] ->
	print_predicate fmt concl
    | Svar (id, v) :: hyps -> 
	fprintf fmt "!%a:%a.@\n" Ident.print id print_cc_type v;
	print_seq fmt hyps
    | Spred (_, p) :: hyps -> 
	fprintf fmt "@[%a@] ==>@\n" print_predicate p;
	print_seq fmt hyps
  in
  fprintf fmt "@[%a@]@?" print_seq hyps

let print_parameter fmt id v =
  fprintf fmt "<parameter ???>"

let print_obligation fmt id sq =
  fprintf fmt "let %s = `%a`;;@\n@\n" id print_sequent sq

let print_elem fmt = function
  | Parameter (id, v) -> print_parameter fmt id v
  | Obligation (s, sq) -> print_obligation fmt s sq

let output_file fwe =
  let sep = "(* DO NOT EDIT BELOW THIS LINE *)" in
  let f = fwe ^ "_why.ml" in
  do_not_edit sep f
    (fun cout ->
       let fmt = formatter_of_out_channel cout in
       Queue.iter (print_elem fmt) elem_q;
       pp_print_flush fmt ())
