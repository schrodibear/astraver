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

(*i $Id: mizar.ml,v 1.4 2003-09-18 20:32:55 filliatr Exp $ i*)

(*s Mizar output *)

open Options
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
  | PTint -> fprintf fmt "Integer"
  | PTbool -> fprintf fmt "Element of BOOLEAN"
  | PTunit -> fprintf fmt "Element of {0}"
  | PTfloat -> fprintf fmt "Real"
  | PTexternal id -> Ident.print fmt id
  | PTarray PTunit -> fprintf fmt "XFinSequence of {0}"
  | PTarray PTbool -> fprintf fmt "XFinSequence of BOOLEAN"
  | PTarray PTint -> fprintf fmt "XFinSequence of INT"
  | PTarray PTfloat -> fprintf fmt "XFinSequence of REAL"
  | PTarray (PTexternal id) -> fprintf fmt "XFinSequence of %a" Ident.print id
  | PTarray (PTarray _) -> assert false

let prefix_id id =
  (* int cmp *)
  if id == t_lt_int then "int_lt" 
  else if id == t_le_int then "int_le"
  else if id == t_gt_int then "int_gt"
  else if id == t_ge_int then "int_ge"
  else if id == t_eq_int then assert false (* TODO *)
  else if id == t_neq_int then assert false (* TODO *)
  (* float cmp *)
  else if id == t_lt_float then "real_lt" 
  else if id == t_le_float then "real_le"
  else if id == t_gt_float then "real_gt"
  else if id == t_ge_float then "real_ge"
  else if id == t_eq_float then assert false (* TODO *)
  else if id == t_neq_float then assert false (* TODO *)
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
  (* float ops *)
  else if id == t_add_float then "real_add"
  else if id == t_sub_float then "real_sub"
  else if id == t_mul_float then "real_mul"
  else if id == t_div_float then "real_div"
  else if id == t_neg_float then "real_neg"
  else if id == t_sqrt_float then assert false (* TODO *)
  else if id == t_float_of_int then assert false (* TODO *)
  else assert false

let rec print_term fmt t = 
  let rec print0 fmt = function
    | Tapp (id, [a; b]) when is_relation id -> 
	fprintf fmt "@[%s(@[%a,@ %a@])@]" 
	  (prefix_id id) print0 a print0 b
    | t ->
	print1 fmt t
  and print1 fmt = function
    | Tapp (id, [a; b]) when id == t_add_int || id == t_add_float ->
	fprintf fmt "%a +@ %a" print1 a print2 b
    | Tapp (id, [a; b]) when id == t_sub_int || id == t_sub_float ->
	fprintf fmt "%a -@ %a" print1 a print2 b
    | t ->
	print2 fmt t
  and print2 fmt = function
    | Tapp (id, [a; b]) when id == t_mul_int || id == t_mul_float ->
	fprintf fmt "%a *@ %a" print2 a print3 b
    | Tapp (id, [a; b]) when id == t_div_int || id == t_div_float ->
	fprintf fmt "%a /@ %a" print2 a print3 b
    | Tapp (id, [a; b]) when id == t_mod_int ->
	fprintf fmt "%a mod %a" print2 a print3 b
    | t -> 
	print3 fmt t
  and print3 fmt = function
    | Tvar id -> 
	Ident.print fmt id
    | Tconst (ConstInt n) -> 
	fprintf fmt "%d" n
    | Tconst (ConstBool true) -> 
	fprintf fmt "TRUE" 
    | Tconst (ConstBool false) -> 
	fprintf fmt "FALSE" 
    | Tconst ConstUnit -> 
	fprintf fmt "(Extract 0)" 
    | Tconst (ConstFloat f) ->
	fprintf fmt "%s" f
    | Tderef _ -> 
	assert false
    (* arithmetic *)
    | Tapp (id, [a]) when id == t_neg_int || id == t_neg_float ->
	fprintf fmt "(@[-%a@])" print3 a
    | Tapp (id, [_;_]) as t when is_relation id || is_int_arith_binop id ->
	fprintf fmt "(@[%a@])" print0 t
    | Tapp (id, [a; b; c]) when id == if_then_else -> 
	fprintf fmt "@[if-then-else(@[%a,@ %a,@ %a@])@]" 
	print0 a print0 b print0 c
    (* arrays *)
    | Tapp (id, [a; b]) when id == access ->
	fprintf fmt "(@[%a.%a@])" print0 b print0 a
    | Tapp (id, [a; b; c]) when id == store ->
	fprintf fmt "(@[%a+*(%a,@ %a)@])" 
	print3 b print0 a print0 c
    | Tapp (id, [a]) when id == Ident.array_length ->
	fprintf fmt "(@[len %a@])" print0 a
    (* any other application *)
    | Tapp (id, tl) when is_relation id || is_arith id -> 
	fprintf fmt "%s(@[%a@])" (prefix_id id) print_terms tl
    | Tapp (id, tl) ->
	fprintf fmt "%a(@[%a@])" Ident.print id print_terms tl
  in
  print0 fmt t

and print_terms fmt tl = 
  print_list comma print_term fmt tl

let infix_relation id =
       if id == t_lt_int || id == t_lt_float then "<" 
  else if id == t_le_int || id == t_le_float then "<="
  else if id == t_gt_int || id == t_gt_float then ">"
  else if id == t_ge_int || id == t_ge_float then ">="
  else if is_eq id then "="
  else if is_neq id then "<>"
  else assert false

let print_predicate fmt p = 
  let rec print0 fmt = function
    | Pimplies (_, a, b) ->
	fprintf fmt "(@[%a implies@ %a@])" print1 a print0 b
    | Pif (a, b, c) ->
	fprintf fmt "(@[(%a = TRUE implies %a) &@ (%a = FALSE implies %a)@])" 
	print_term a print0 b print_term a print0 c
    | p -> 
	print1 fmt p
  and print1 fmt = function
    | Por (a, b) ->
	fprintf fmt "@[%a or@ %a@]" print2 a print1 b
    | p ->
	print2 fmt p
  and print2 fmt = function
    | Pand (_, a, b) | Forallb (_, _, _, _, a, b) ->
	fprintf fmt "@[%a &@ %a@]" print3 a print2 b
    | p ->
	print3 fmt p
  and print3 fmt = function
    | Ptrue ->
	fprintf fmt "not contradiction"
    | Pvar id when id == default_post ->
	fprintf fmt "not contradiction"
    | Pfalse ->
	fprintf fmt "contradiction"
    | Pvar id -> 
	fprintf fmt "%a" Ident.print id
    | Papp (id, [a; b]) when is_relation id ->
	fprintf fmt "@[%a %s@ %a@]" 
	print_term a (infix_relation id) print_term b
    | Papp (id, [a; b]) when id == t_zwf_zero ->
	fprintf fmt "@[(0 <= %a &@ %a < %a)@]" 
	print_term b print_term a print_term b
    | Papp (id, tl) when is_relation id || is_arith id ->
	fprintf fmt "@[%s(%a)@]" (prefix_id id) print_terms tl
    | Papp (id, tl) -> 
	fprintf fmt "@[%a(%a)@]" Ident.print id print_terms tl
    | Pnot a ->
	fprintf fmt "@[not %a@]" print3 a
    | Forall (_,id,n,t,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = subst_in_predicate (subst_onev n id') p in
	fprintf fmt "(@[for %s being %a@ holds %a@])" (Ident.string id')
	  print_pure_type t print0 p'
    | Exists (id,n,t,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = subst_in_predicate (subst_onev n id') p in
	fprintf fmt "(@[ex %s being %a st@ %a@])" (Ident.string id')
	  print_pure_type t print0 p'
    | (Por _ | Pand _ | Pif _ | Pimplies _ | Forallb _) as p -> 
	fprintf fmt "(%a)" print0 p
  in
  print0 fmt p

let rec print_cc_type fmt = function
  | TTpure pt -> 
      print_pure_type fmt pt
  | TTarray (TTpure pt) -> 
      print_pure_type fmt (PTarray pt)
  | _ ->
      assert false

let print_sequent fmt (hyps,concl) =
  let rec print_seq fmt = function
    | [] ->
	print_predicate fmt concl
    | Svar (id, v) :: hyps -> 
	fprintf fmt "@[for %a being @[%a@] holds@]@\n" 
	  Ident.print id print_cc_type v;
	print_seq fmt hyps
    | Spred (_, p) :: hyps -> 
	fprintf fmt "@[(@[%a@]) %s@]@\n" print_predicate p
	  (match hyps with Spred _ :: _ -> "&" | _ -> "implies");
	print_seq fmt hyps
  in
  let print_intro fmt = function
    | Svar (id, v) -> 
	fprintf fmt "let %a be @[%a@];@\n" Ident.print id print_cc_type v
    | Spred (id, p) -> 
	fprintf fmt "assume %a: @[%a@];@\n" Ident.print id print_predicate p
  in
  let print_intros fmt = List.iter (print_intro fmt) in
  fprintf fmt "@[  @[%a@]@\nproof@\n  @[%a@]:: EDIT BELOW THIS LINE@\n@]" 
    print_seq hyps print_intros hyps

let reprint_obligation fmt (loc,id,s) =
  fprintf fmt "@[  :: %a @]@\n" Loc.report_obligation loc;
  fprintf fmt "@[  theorem %s: @\n  @[%a@]@]" id print_sequent s

let print_obligation fmt o = 
  reprint_obligation fmt o;
  fprintf fmt "  :: FILL PROOF HERE@\n    thus thesis;@\n  end;@\n"

let reprint_parameter fmt id c =
  fprintf fmt 
    "@[<hov 2>  :: Why Parameter (TODO)@]@\n" (* id print_cc_type c *)

let print_parameter = reprint_parameter

open Regen

module Gen = Regen.Make(
struct

  let print_element fmt e = 
    begin match e with
      | Parameter (id, c) -> print_parameter fmt id c
      | Obligation o -> print_obligation fmt o
    end;
    fprintf fmt "@\n"
      
  let reprint_element fmt = function
    | Parameter (id, c) -> reprint_parameter fmt id c
    | Obligation o -> reprint_obligation fmt o

  let re_oblig_loc = Str.regexp ":: Why obligation from .*"

  let first_time fmt =
    fprintf fmt "\
:: This file was originally generated by why.
:: It can be modified; only the generated parts will be overwritten. 
environ
  %s
begin :: proof obligations start here
" mizar_preamble

  let edit_below = Str.regexp "[ ]*:: EDIT BELOW THIS LINE[ ]*"
  let end_of_element _ s = Str.string_match edit_below s 0

end)

let reset = Gen.reset

let push_obligations = 
  List.iter (fun ((_,l,_) as o) -> Gen.add_elem (Oblig, l) (Obligation o))

let push_parameter id v =
  Gen.add_elem (Param, id) (Parameter (id,v))

let _ = 
  Gen.add_regexp 
    "Lemma[ ]+\\(.*_po_[0-9]+\\)[ ]*:[ ]*" Oblig;
  Gen.add_regexp 
    "Definition[ ]+\\([^ ]*\\)[ ]*:=[ ]*(\\* validation \\*)[ ]*" Valid;
  Gen.add_regexp 
    "Definition[ ]+\\([^ ]*\\)[ ]*(\\* validation \\*)[ ]*" Valid;
  Gen.add_regexp 
    "(\\*Why\\*) Parameter[ ]+\\([^ ]*\\)[ ]*:[ ]*" Param

let output_file fwe =
  let f = fwe ^ "_why.miz" in
  Gen.output_file f
