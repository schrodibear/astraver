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

(*i $Id: simplify.ml,v 1.3 2003-10-21 15:55:35 filliatr Exp $ i*)

(*s Simplify's output *)

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

let prefix id =
  if id == t_lt then "<"
  else if id == t_le then "<="
  else if id == t_gt then ">"
  else if id == t_ge then ">="
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
  (* float ops *)
  else if id == t_add_float 
       || id == t_sub_float 
       || id == t_mul_float 
       || id == t_div_float 
       || id == t_neg_float 
       || id == t_sqrt_float 
       || id == t_float_of_int 
  then
    Report.raise_unlocated (AnyMessage "Simplify does not support floats")
  else assert false

let rec print_term fmt = function
  | Tvar id -> 
      fprintf fmt "%a" Ident.print id
  | Tconst (ConstInt n) -> 
      fprintf fmt "%d" n
  | Tconst (ConstBool b) -> 
      fprintf fmt "|@@%b|" b
  | Tconst ConstUnit -> 
      fprintf fmt "tt" (* TODO: CORRECT? *)
  | Tconst (ConstFloat _) ->
      Report.raise_unlocated (AnyMessage "Simplify does not support floats")
  | Tderef _ -> 
      assert false
  | Tapp (id, [a; b; c]) when id == if_then_else ->
      assert false; (* SUPPORTED IN SIMPLIFY? *)
      (*
      fprintf fmt "@[(ite@ %a@ %a@ %a)@]" print_term a print_term b
	print_term c *)
  | Tapp (id, [a; b]) when id == access ->
      fprintf fmt "@[(select@ %a@ %a)@]" print_term a print_term b
  | Tapp (id, [a; b; c]) when id == store ->
      fprintf fmt "@[(store@ %a@ %a@ %a)@]" 
	print_term a print_term b print_term c
  | Tapp (id, tl) when is_relation id || is_arith id ->
      fprintf fmt "@[(%s %a)@]" (prefix id) print_terms tl
  | Tapp (id, tl) ->
      fprintf fmt "@[(%a@ %a)@]" 
	Ident.print id (print_list space print_term) tl

and print_terms fmt tl = 
  print_list space print_term fmt tl

let external_type = function
  | PTexternal _ | PTarray (PTexternal _) -> true
  | _ -> false

let has_type ty fmt id = match ty with
  | PTexternal ty ->
      fprintf fmt "(EQ (IS%a %a) |@@true|)" Ident.print ty Ident.print id
  | PTarray (PTexternal ty) ->
      fprintf fmt "(FORALL (k) (EQ (IS%a (select %a k)) |@@true|))" 
	Ident.print ty Ident.print id
  | _ -> 
      assert false

let rec print_predicate fmt = function
  | Ptrue ->
      fprintf fmt "TRUE"
  | Pvar id when id == default_post ->
      fprintf fmt "TRUE"
  | Pfalse ->
      fprintf fmt "FALSE"
  | Pvar id -> 
      fprintf fmt "%a" Ident.print id
  | Papp (id, [a; b]) when is_eq id ->
      fprintf fmt "@[(EQ %a@ %a)@]" print_term a print_term b
  | Papp (id, [a; b]) when is_neq id ->
      fprintf fmt "@[(NEQ %a@ %a)@]" print_term a print_term b
  | Papp (id, tl) when is_relation id || is_arith id ->
      fprintf fmt "@[(%s %a)@]" (prefix id) print_terms tl
  | Papp (id, [a;b]) when id == t_zwf_zero ->
      fprintf fmt "@[(AND (<= 0 %a)@ (< %a %a))@]" 
	print_term b print_term a print_term b
  | Papp (id, tl) -> 
      fprintf fmt "@[(EQ (%a@ %a) |@@true|)@]" Ident.print id print_terms tl
  | Pimplies (_, a, b) ->
      fprintf fmt "@[(IMPLIES@ %a@ %a)@]" print_predicate a print_predicate b
  | Pif (a, b, c) ->
      fprintf fmt 
     "@[(AND@ (IMPLIES (EQ %a |@@true|) %a)@ (IMPLIES (EQ %a |@@false|) %a))@]"
      print_term a print_predicate b print_term a print_predicate c
  | Pand (_, a, b) | Forallb (_, _, _, _, a, b) ->
      fprintf fmt "@[(AND@ %a@ %a)@]" print_predicate a print_predicate b
  | Por (a, b) ->
      fprintf fmt "@[(OR@ %a@ %a)@]" print_predicate a print_predicate b
  | Pnot a ->
      fprintf fmt "@[(NOT@ %a)@]" print_predicate a
  | Forall (_, id, n, ty, p) when external_type ty -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(FORALL (%a) (IMPLIES %a@ %a))@]" 
	Ident.print id' (has_type ty) id' print_predicate p'
  | Forall (_,id,n,_,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(FORALL (%a)@ %a)@]" Ident.print id' print_predicate p'
  | Exists (id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(EXISTS (%a)@ %a)@]" Ident.print id' print_predicate p'

let cc_external_type = function
  | Cc.TTpure ty -> external_type ty
  | Cc.TTarray (Cc.TTpure (PTexternal _)) -> true
  | _ -> false

let cc_has_type ty fmt id = match ty with
  | Cc.TTpure ty when external_type ty ->
      has_type ty fmt id
  | Cc.TTarray (Cc.TTpure (PTexternal ty)) ->
      fprintf fmt "(FORALL (k) (EQ (IS%a (select %a k)) |@@true|))" 
	Ident.print ty Ident.print id
  | _ -> 
      assert false

let print_sequent fmt (hyps,concl) =
  let rec print_seq fmt = function
    | [] ->
	print_predicate fmt concl
    | Svar (id, ty) :: hyps when cc_external_type ty -> 
	fprintf fmt "@[(FORALL (%a) (IMPLIES %a@ %a))@]" 
	  Ident.print id (cc_has_type ty) id print_seq hyps
    | Svar (id, v) :: hyps -> 
	fprintf fmt "@[(FORALL (%a)@ %a)@]" Ident.print id print_seq hyps
    | Spred (_,p) :: hyps -> 
	fprintf fmt "@[(IMPLIES %a@ %a)@]" print_predicate p print_seq hyps
  in
  print_seq fmt hyps

let print_obligation fmt (loc, o, s) = 
  fprintf fmt "@[;; %s, %a@]@\n" o Loc.report_obligation loc;
  fprintf fmt "@[<hov 2>%a@]@\n@\n" print_sequent s

let prelude = ref 
"(BG_PUSH (FORALL (t i v) (EQ (array_length (store t i v)) (array_length t))))"

let output_file fwe =
  let sep = ";; DO NOT EDIT BELOW THIS LINE" in
  let f = fwe ^ "_why.sx" in
  do_not_edit f
    (fun fmt -> fprintf fmt "@[%s@]@\n" !prelude)
    sep
    (fun fmt -> Queue.iter (print_obligation fmt) oblig)

