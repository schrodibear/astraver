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

(*i $Id: holl.ml,v 1.1 2003-01-09 13:13:47 filliatr Exp $ i*)

(*s HOL Light output *)

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

let rec print_term fmt = function
  | Tvar id -> 
      Ident.print fmt id
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
  | Tapp (id, tl) when is_relation id || is_arith id ->
      fprintf fmt "@[(%s %a)@]" (prefix id) print_terms tl
  | Tapp (id, tl) ->
      fprintf fmt "@[(%a@ %a)@]" 
	uncapitalize id (print_list space print_term) tl

and print_terms fmt tl = 
  print_list space print_term fmt tl

let rec print_predicate fmt = function
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
  | Ptrue ->
      fprintf fmt "true"
  | Pfalse ->
      fprintf fmt "false"
  | Pimplies (a, b) ->
      fprintf fmt "@[(->@ %a@ %a)@]" print_predicate a print_predicate b
  | Pif (a, b, c) ->
      fprintf fmt "@[(ite@ %a@ %a@ %a)@]" print_term a print_predicate b
	print_predicate c
  | Pand (a, b) ->
      fprintf fmt "@[(and@ %a@ %a)@]" print_predicate a print_predicate b
  | Por (a, b) ->
      fprintf fmt "@[(or@ %a@ %a)@]" print_predicate a print_predicate b
  | Pnot a ->
      fprintf fmt "@[(not@ %a)@]" print_predicate a
  | Forall _
  | Exists _ -> assert false

let output_sequent fmt (ctx, c) = match ctx with
  | [] -> 
      fprintf fmt "@[%a@]" print_predicate c
  | [p] -> 
      fprintf fmt "@[<hov 2>(->@ @[%a@]@ %a)@]" 
	print_predicate p print_predicate c
  | ctx -> 
      fprintf fmt "@[<hov 2>(->@ @[<hov 2>(and@ %a)@]@ %a)@]"
	(print_list space print_predicate) ctx print_predicate c
