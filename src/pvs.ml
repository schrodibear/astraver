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

(*i $Id: pvs.ml,v 1.35 2003-01-24 13:53:48 filliatr Exp $ i*)

open Logic
open Types
open Cc
open Misc
open Util
open Ident
open Format
open Vcg

let relation id =
  if id == t_lt then "<" 
  else if id == t_le then "<="
  else if id == t_gt then ">"
  else if id == t_ge then ">="
  else if id == t_eq then "="
  else if id == t_neq then "/="
  else assert false

let print_term fmt t = 
  let rec print0 fmt = function
    | Tapp (id, [a;b]) when is_relation id ->
	fprintf fmt "@[<hov 2>%a %s@ %a@]" print1 a (relation id) print1 b
    | t -> 
	print1 fmt t
  and print1 fmt = function
    | Tapp (id, [a;b]) when id == t_add_int || id == t_sub_int ->
	fprintf fmt "@[<hov 2>%a %s@ %a@]" 
	  print1 a (if id == t_add_int then "+" else "-") print2 b
    | t ->
	print2 fmt t
  and print2 fmt = function
    | Tapp (id, [a;b]) when id == t_mul_int || id == t_div_int ->
	fprintf fmt "@[<hov 2>%a %s@ %a@]" 
	  print2 a (if id == t_mul_int then "*" else "/") print3 b
    | t ->
	print3 fmt t
  and print3 fmt = function
    | Tconst (ConstInt n) -> 
	fprintf fmt "%d" n
    | Tconst (ConstBool b) -> 
	fprintf fmt "%b" b
    | Tconst ConstUnit -> 
	fprintf fmt "unit" 
    | Tconst (ConstFloat f) -> 
	let n,d = rationalize f in
	if d = "1" then fprintf fmt "%s" n else fprintf fmt "%s/%s" n d
    | Tderef _ ->
	assert false
    | Tvar id when id == t_zwf_zero ->
	fprintf fmt "zwf_zero"
    | Tvar id | Tapp (id, []) -> 
	fprintf fmt "%s" (Ident.string id)
    | Tapp (id, [t]) when id == t_neg_int ->
	fprintf fmt "-%a" print3 t
    | Tapp (id, [a; b; c]) when id == if_then_else -> 
	fprintf fmt "(@[if %a@ then %a@ else %a@])" print0 a print0 b print0 c
    | Tapp (id, l) as t when is_relation id || is_int_arith id ->
	fprintf fmt "@[(%a)@]" print0 t
    | Tapp (id, tl) -> 
	fprintf fmt "%s(@[%a@])" 
	  (Ident.string id) (print_list comma print0) tl
  in
  print0 fmt t

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "int"
  | PTbool -> fprintf fmt "bool"
  | PTunit -> fprintf fmt "unit"
  | PTfloat -> fprintf fmt "real"
  | PTarray v -> fprintf fmt "warray[%a]" print_pure_type v
  | PTexternal id -> fprintf fmt "%s" (Ident.string id)

let infix_relation id =
  if id == t_lt_int then "<" 
  else if id == t_le_int then "<="
  else if id == t_gt_int then ">"
  else if id == t_ge_int then ">="
  else if id == t_eq_int then "="
  else if id == t_neq_int then "/="
  else assert false

let print_predicate fmt p =
  let rec print0 = function
    | Pif (a, b, c) -> 
	fprintf fmt "@[IF "; print_term fmt a; fprintf fmt "@ THEN ";
	print0 b; fprintf fmt "@ ELSE "; print0 c; fprintf fmt " ENDIF@]"
    | Pimplies (a, b) -> 
	fprintf fmt "(@["; print1 a; fprintf fmt " IMPLIES@ "; print0 b;
	fprintf fmt "@])"
    | p -> print1 p
  and print1 = function
    | Por (a, b) -> print1 a; fprintf fmt " OR@ "; print2 b
    | p -> print2 p
  and print2 = function
    | Pand (a, b) -> print2 a; fprintf fmt " AND@ "; print3 b
    | p -> print3 p
  and print3 = function
    | Pfalse ->
	fprintf fmt "False"
    | Ptrue ->
	fprintf fmt "True"
    | Pvar id when id == default_post ->
	fprintf fmt "False"
    | Pvar id -> 
	Ident.print fmt id
    | Papp (id, [t]) when id == well_founded ->
	fprintf fmt "well_founded?(%a)" print_term t
    | Papp (id, [a;b]) when id == t_zwf_zero ->
	fprintf fmt "zwf_zero(%a, %a)" print_term a print_term b
    | Papp (id, [a;b]) when is_int_comparison id ->
	fprintf fmt "%a %s@ %a" print_term a (infix_relation id) print_term b
    | Papp (id, [a;b]) when is_eq id ->
	fprintf fmt "%a =@ %a" print_term a print_term b
    | Papp (id, [a;b]) when is_neq id ->
	fprintf fmt "%a /=@ %a" print_term a print_term b
    | Papp (id, l) -> 	
	fprintf fmt "%s(@[" (Ident.string id);
	print_list (fun fmt () -> fprintf fmt ",@ ") print_term fmt l;
	fprintf fmt "@])"
    | Pnot p -> 
	fprintf fmt "NOT "; print3 p
    | Forall (id,n,t,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = subst_in_predicate (subst_onev n id') p in
	fprintf fmt "(@[FORALL (%s: " (Ident.string id');
	print_pure_type fmt t; fprintf fmt "):@ ";
	print0 p'; fprintf fmt "@])"
    | Exists (id,n,t,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = subst_in_predicate (subst_onev n id') p in
	fprintf fmt "(@[EXIST (%s: " (Ident.string id');
	print_pure_type fmt t; fprintf fmt "):@ ";
	print0 p'; fprintf fmt "@])"
    | p -> 
	fprintf fmt "("; print0 p; fprintf fmt ")"
  in
  print0 p

let rec print_cc_type fmt = function
  | TTpure pt -> print_pure_type fmt pt
  | TTarray v -> fprintf fmt "warray[%a]" print_cc_type v
  | TTarrow ((_, CC_var_binder t1), t2) ->
      fprintf fmt "[%a -> %a]" print_cc_type t1 print_cc_type t2
  | TTterm t -> print_term fmt t
  | TTtuple _ 
  | TTpred _ 
  | TTlambda _
  | TTarrow _
  | TTapp _ -> assert false

let print_sequent fmt (hyps,concl) =
  let rec print_seq = function
    | [] ->
	print_predicate fmt concl
    | Svar (id, v) :: hyps -> 
	fprintf fmt "FORALL (%a: %a) :@\n" Ident.print id print_cc_type v;
	print_seq hyps
    | Spred (_,p) :: hyps -> 
	print_predicate fmt p; fprintf fmt " IMPLIES@\n";
	print_seq hyps
  in
  print_seq hyps

let print_lemma fmt (_,id,s) =
  fprintf fmt "  @[<hov 2>%s: LEMMA@\n" id;
  print_sequent fmt s;
  fprintf fmt "@]@\n"

let print_obligations fmt ol = 
  print_list (fun fmt () -> fprintf fmt "@\n") print_lemma fmt ol;
  if ol <> [] then fprintf fmt "@\n"

let begin_theory fmt th =
  fprintf fmt "%s_why: THEORY@\nBEGIN@\n@\n" th;
  fprintf fmt "  importing why@@why@\n"
    
let end_theory fmt th =
  fprintf fmt "END %s_why@\n" th

let print_parameter fmt id v =
  fprintf fmt "  %s: VAR @[%a@]@\n@\n" id print_cc_type v

type elem = 
  | Verbatim of string
  | Obligations of obligation list
  | Parameter of string * cc_type

let queue = Queue.create ()

let reset () = Queue.clear queue

let push_obligations ol = Queue.add (Obligations ol) queue

let push_parameter id v = Queue.add (Parameter (id,v)) queue

let output_elem fmt = function
  | Verbatim s -> fprintf fmt "  %s@\n@\n" s
  | Obligations ol -> print_obligations fmt ol
  | Parameter (id, v) -> print_parameter fmt id v

let output_file fwe =
  let sep = "  %% DO NOT EDIT BELOW THIS LINE" in
  let f = fwe ^ "_why.pvs" in
  let th = Filename.basename fwe in
  do_not_edit f
    (fun fmt ->
       begin_theory fmt th)
    sep
    (fun fmt ->
       Queue.iter (output_elem fmt) queue;
       end_theory fmt th)
