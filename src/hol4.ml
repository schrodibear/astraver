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

(*i $Id: hol4.ml,v 1.5 2005-11-18 14:54:08 filliatr Exp $ i*)

(*s HOL 4 output (contributed by Seungkeol Choe, University of Utah) *)

open Ident
open Misc
open Error
open Logic
open Vcg
open Format
open Cc
open Pp

type elem = 
  | Parameter of string * cc_type
  | Obligation of obligation
  | Logic of string * logic_type Env.scheme
  | Axiom of string * predicate Env.scheme
  | Predicate of string * predicate_def Env.scheme

let elem_q = Queue.create ()

let reset () = Queue.clear elem_q

let push_parameter id v = Queue.add (Parameter (id, v)) elem_q

let push_logic id t = Queue.add (Logic (id, t)) elem_q

let push_axiom id p = Queue.add (Axiom (id, p)) elem_q

let push_predicate id p = Queue.add (Predicate (id, p)) elem_q

let push_obligations = List.iter (fun o -> Queue.add (Obligation o) elem_q)

(*s Pretty print *)

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "int"
  | PTbool -> fprintf fmt "bool"
  | PTunit -> fprintf fmt "one"
  | PTreal -> fprintf fmt "real"
  | PTexternal([v],id) when id==farray -> 
      fprintf fmt "list(%a)" print_pure_type v (* TODO *)
  | PTexternal([],id) -> Ident.print fmt id
  | PTexternal(_,_) 
  | PTvar _ -> failwith "no polymorphism with HOL4 yet"
  | PTvarid _ -> assert false

let prefix_id id =
  (* int cmp *)
  if id == t_lt_int then "int_lt" 
  else if id == t_le_int then "int_le"
  else if id == t_gt_int then "int_gt"
  else if id == t_ge_int then "int_ge"
  else if id == t_eq_int then assert false (* TODO *)
  else if id == t_neq_int then assert false (* TODO *)
  (* real cmp *)
  else if id == t_lt_real then "real_lt" 
  else if id == t_le_real then "real_le"
  else if id == t_gt_real then "real_gt"
  else if id == t_ge_real then "real_ge"
  else if id == t_eq_real then assert false (* TODO *)
  else if id == t_neq_real then assert false (* TODO *)
  (* bool cmp *)
  else if id == t_eq_bool then assert false (* TODO *)
  else if id == t_neq_bool then assert false (* TODO *)
  (* unit cmp *)
  else if id == t_eq_unit then assert false (* TODO *)
  else if id == t_neq_unit then assert false (* TODO *)
  (* int ops *)
  else if id == t_add_int then "int_add"
  else if id == t_sub_int then "int_sub"
  else if id == t_mul_int then "int_mul"
  else if id == t_div_int then assert false (* TODO *)
  else if id == t_mod_int then assert false (* TODO *)
  else if id == t_neg_int then "int_neg"
  (* real ops *)
  else if id == t_add_real then "real_add"
  else if id == t_sub_real then "real_sub"
  else if id == t_mul_real then "real_mul"
  else if id == t_div_real then "real_div"
  else if id == t_neg_real then "real_neg"
  else if id == t_sqrt_real then assert false (* TODO *)
  else if id == t_real_of_int then assert false (* TODO *)
  else assert false

let rec print_term fmt = function
  | Tvar id -> 
      Ident.print fmt id
  | Tconst (ConstInt n) -> 
      fprintf fmt "%s" n
  | Tconst (ConstBool true) -> 
      fprintf fmt "T" 
  | Tconst (ConstBool false) -> 
      fprintf fmt "F" 
  | Tconst ConstUnit -> 
      fprintf fmt "one" 
  | Tconst (ConstFloat (i,f,e)) ->
      let e = (if e = "" then 0 else int_of_string e) - String.length f in
      if e = 0 then
	fprintf fmt "(real_of_num %s%s)" i f
      else if e > 0 then
	fprintf fmt "(real_of_num (%s%s * 1%s))" i f (String.make e '0')
      else
	fprintf fmt "(real_of_num %s%s / real_of_num 1%s)" 
	  i f (String.make (-e) '0')
  | Tderef _ -> 
      assert false
  (* arithmetic *)
  | Tapp (id, [a; b], _) when id == t_add_int || id == t_add_real ->
      fprintf fmt "(@[%a +@ %a@])" print_term a print_term b
  | Tapp (id, [a; b], _) when id == t_sub_int || id == t_sub_real ->
      fprintf fmt "(@[%a -@ %a@])" print_term a print_term b
  | Tapp (id, [a; b], _) when id == t_mul_int || id == t_mul_real ->
      fprintf fmt "(@[%a *@ %a@])" print_term a print_term b
  | Tapp (id, [a; b], _) when id == t_div_real ->
      fprintf fmt "(@[%a /@ %a@])" print_term a print_term b
  | Tapp (id, [a], _) when id == t_neg_int || id == t_neg_real ->
      fprintf fmt "(@[--%a@])" print_term a
  | Tapp (id, [a; b; c], _) when id == if_then_else -> 
      fprintf fmt "(@[if %a@ then %a@ else %a@])" 
	print_term a print_term b print_term c
  | Tapp (id, tl, _) when is_relation id || is_arith id -> 
      fprintf fmt "(@[%s %a@])" (prefix_id id) print_terms tl
  (* arrays *)
  | Tapp (id, [a; b], _) when id == access ->
      fprintf fmt "(@[EL (num_of_int %a) %a@])" print_term b print_term a
  | Tapp (id, [a], _) when id == Ident.array_length ->
      fprintf fmt "(@[LENGTH %a@])" print_term a
  (* any other application *)
  | Tapp (id, tl, _) ->
      fprintf fmt "@[(%a@ %a)@]" 
	Ident.print id (print_list space print_term) tl

and print_terms fmt tl = 
  print_list space print_term fmt tl

let rec print_predicate fmt = function
  | Ptrue ->
      fprintf fmt "T"
  | Pvar id when id == Ident.default_post ->
      fprintf fmt "T"
  | Pfalse ->
      fprintf fmt "F"
  | Pvar id -> 
      fprintf fmt "%a" Ident.print id
  | Papp (id, [a; b], _) when is_eq id ->
      fprintf fmt "@[(%a =@ %a)@]" print_term a print_term b
  | Papp (id, [a; b], _) when is_neq id ->
      fprintf fmt "@[~(%a =@ %a)@]" print_term a print_term b
  | Papp (id, [a; b], _) when id == t_lt_int || id == t_lt_real ->
      fprintf fmt "@[(%a <@ %a)@]" print_term a print_term b
  | Papp (id, [a; b], _) when id == t_le_int || id == t_le_real ->
      fprintf fmt "@[(%a <=@ %a)@]" print_term a print_term b
  | Papp (id, [a; b], _) when id == t_gt_int || id == t_gt_real ->
      fprintf fmt "@[(%a >@ %a)@]" print_term a print_term b
  | Papp (id, [a; b], _) when id == t_ge_int || id == t_ge_real ->
      fprintf fmt "@[(%a >=@ %a)@]" print_term a print_term b
  | Papp (id, [a; b], _) when id == t_zwf_zero ->
      fprintf fmt "@[((0 <= %a) /\\@ (%a < %a))@]" 
	print_term b print_term a print_term b
  | Papp (id, tl, _) when is_relation id || is_arith id ->
      fprintf fmt "@[(%s %a)@]" (prefix_id id) print_terms tl
  | Papp (id, tl, _) -> 
      fprintf fmt "@[(%a@ %a)@]" Ident.print id print_terms tl
  | Pimplies (_, a, b) ->
      fprintf fmt "(@[%a ==>@ %a@])" print_predicate a print_predicate b
  | Piff (a, b) ->
      fprintf fmt "(@[(@[%a ==>@ %a@]) /\\@ (@[%a ==>@ %a@])@])" 
	print_predicate a print_predicate b
	print_predicate b print_predicate a
  | Pif (a, b, c) ->
      fprintf fmt "(@[if %a@ then %a@ else %a@])" 
	print_term a print_predicate b print_predicate c
  | Pand (_, _, a, b) | Forallb (_, a, b) ->
      fprintf fmt "@[(%a /\\@ %a)@]" print_predicate a print_predicate b
  | Por (a, b) ->
      fprintf fmt "@[(%a \\/@ %a)@]" print_predicate a print_predicate b
  | Pnot a ->
      fprintf fmt "@[~(%a)@]" print_predicate a
  | Forall (_,id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "(@[!%s:%a.@ %a@])" (Ident.string id')
	print_pure_type t print_predicate p'
  | Exists (id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "(@[?%s:%a.@ %a@])" (Ident.string id')
	print_pure_type t print_predicate p'
  | Pfpi _ ->
      failwith "fpi not supported in HOL Light"
  | Pnamed (n, p) ->
      fprintf fmt "@[(* %s: *) %a@]" n print_predicate p

let rec print_cc_type fmt = function
  | TTpure pt -> 
      print_pure_type fmt pt
  | TTarray v -> 
      fprintf fmt "(@[%a list@])" print_cc_type v
  | _ ->
      assert false

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

(* TODO *)
let print_parameter fmt id v =
  fprintf fmt "(* parameter %s *);;" id

(* TODO *)
let print_logic fmt id t =
  let (l,t) = Env.specialize_logic_type t in
  fprintf fmt "(* logic %s *);;" id

(* TODO *)
let print_axiom fmt id v =
  fprintf fmt "(* axiom %s *);;" id

let print_obligation fmt loc id sq =
  fprintf fmt "@[(* %a *)@]@\n" Loc.report_obligation_position loc;
  fprintf fmt "val %s = Parse.Term `%a`;;@\n@\n" id print_sequent sq

let print_elem fmt = function
  | Parameter (id, v) -> print_parameter fmt id v
  | Obligation (loc, s, sq) -> print_obligation fmt loc s sq
  | Logic (id, t) -> print_logic fmt id t
  | Axiom (id, p) -> print_axiom fmt id p
  | Predicate _ -> assert false (*TODO*)

let print_obl_list fmt = 
  let comma = ref false in
  let print = function
    | Obligation (_,id,_) -> 
	if !comma then fprintf fmt "; "; fprintf fmt "%s" id; comma := true
    | Parameter _ | Axiom _ | Logic _ | Predicate _ -> 
	()
  in
  fprintf fmt "val all = ["; 
  Queue.iter print elem_q;
  fprintf fmt "]@\n"

let output_file fwe =
  let sep = "(* DO NOT EDIT BELOW THIS LINE *)" in
  let f = fwe ^ "_why.ml" in
  do_not_edit f 
    (fun _ -> ())
    sep 
    (fun fmt ->
       fprintf fmt "load \"intLib\"; \n intLib.prefer_int();\n\n";
       Queue.iter (print_elem fmt) elem_q;
       print_obl_list fmt)
