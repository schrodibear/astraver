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

(*i $Id: coq.ml,v 1.69 2002-10-31 12:27:00 filliatr Exp $ i*)

open Options
open Logic
open Types
open Cc
open Ident
open Util
open Format
open Vcg
open Misc

let out_file f = f ^ "_why.v"

let prefix_id id =
  (* int cmp *)
  if id == t_lt_int then "Z_lt_ge_bool" 
  else if id == t_le_int then "Z_le_gt_bool"
  else if id == t_gt_int then "Z_gt_le_bool"
  else if id == t_ge_int then "Z_ge_lt_bool"
  else if id == t_eq_int then "Z_eq_bool"
  else if id == t_neq_int then "Z_noteq_bool"
  (* float cmp *)
  else if id == t_lt_float then "R_lt_ge_bool" 
  else if id == t_le_float then "R_le_gt_bool"
  else if id == t_gt_float then "R_gt_le_bool"
  else if id == t_ge_float then "R_ge_lt_bool"
  else if id == t_eq_float then "R_eq_bool"
  else if id == t_neq_float then "R_noteq_bool"
  (* int ops *)
  else if id == t_add_int then "Zplus"
  else if id == t_sub_int then "Zminus"
  else if id == t_mul_int then "Zmult"
  else if id == t_div_int then "Zdiv"
  else if id == t_mod_int then "Zmod"
  else if id == t_neg_int then "Zopp"
  (* float ops *)
  else if id == t_add_float then "Rplus"
  else if id == t_sub_float then "Rminus"
  else if id == t_mul_float then "Rmult"
  else if id == t_div_float then "Rdiv"
  else if id == t_neg_float then "Ropp"
  else if id == t_sqrt_float then "sqrt"
  else if id == t_float_of_int then "IZR"
  else assert false

let inz = ref 0
let openz fmt = if !inz == 0 then fprintf fmt "`@["; incr inz 
let closez fmt = decr inz; if !inz == 0 then fprintf fmt "@]`"

let print_term fmt t = 
  let rec print0 fmt = function
    | Tapp (id, [a;b]) when is_relation id ->
	fprintf fmt "(@[<hov 2>%s@ %a@ %a@])" (prefix_id id)
	print1 a print1 b
    | t -> 
	print1 fmt t
  and print1 fmt = function
    | Tapp (id, [a;b]) when id == t_add_int ->
	openz fmt; fprintf fmt "%a +@ %a" print1 a print2 b; closez fmt
    | Tapp (id, [a;b]) when id == t_sub_int ->
	openz fmt; fprintf fmt "%a -@ %a" print1 a print2 b; closez fmt
    | t ->
	print2 fmt t
  and print2 fmt = function
    | Tapp (id, [a;b]) when id == t_mul_int ->
	openz fmt; fprintf fmt "%a *@ %a" print2 a print3 b; closez fmt
    | Tapp (id, [a;b]) when id == t_div_int ->
	fprintf fmt "(@[Zdiv %a@ %a@])" print2 a print3 b
    | Tapp (id, [a;b]) when id == t_mod_int ->
	fprintf fmt "(@[Zmod %a@ %a@])" print2 a print3 b
    | t ->
	print3 fmt t
  and print3 fmt = function
    | Tconst (ConstInt n) -> 
	openz fmt; fprintf fmt "%d" n; closez fmt
    | Tconst (ConstBool b) -> 
	fprintf fmt "%b" b
    | Tconst ConstUnit -> 
	fprintf fmt "tt" 
    | Tconst (ConstFloat f) -> 
	assert (!inz == 0); (* TODO: floats inside integer expressions *)
	let n,d = rationalize f in
	let pint fmt s = openz fmt; fprintf fmt "%s" s; closez fmt in
	if d = "1" then fprintf fmt "(IZR %a)" pint n
	else fprintf fmt "(Rdiv (IZR %a) (IZR %a))" pint n pint d
    | Tvar id when id == implicit ->
	fprintf fmt "?"
    | Tvar id when id == t_zwf_zero ->
	fprintf fmt "(Zwf ZERO)"
    | Tvar id | Tapp (id, []) -> 
	Ident.print fmt id
    | Tapp (id, [t]) when id == t_neg_int ->
	openz fmt; fprintf fmt "(-%a)" print3 t; closez fmt
    | Tapp (id, [_;_]) as t when is_relation id || is_int_arith_binop id ->
	fprintf fmt "@[(%a)@]" print0 t
    | Tapp (id, tl) when id == t_zwf_zero -> 
	fprintf fmt "(@[Zwf 0 %a@])" print_terms tl
    | Tapp (id, tl) when is_relation id || is_arith id -> 
	fprintf fmt "(@[%s %a@])" (prefix_id id) print_terms tl
    | Tapp (id, tl) -> 
	fprintf fmt "(@[%s %a@])" (Ident.string id) print_terms tl
  and print_terms fmt tl =
    print_list space print0 fmt tl
  in
  print0 fmt t

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "Z"
  | PTbool -> fprintf fmt "bool"
  | PTunit -> fprintf fmt "unit"
  | PTfloat -> fprintf fmt "R"
  | PTarray (s, v) -> 
      fprintf fmt "(array %a %a)" print_term s print_pure_type v
  | PTexternal id -> Ident.print fmt id

let infix_relation id =
       if id == t_lt_int then "<" 
  else if id == t_le_int then "<="
  else if id == t_gt_int then ">"
  else if id == t_ge_int then ">="
  else if id == t_eq_int then "="
  else if id == t_neq_int then "<>"
  else assert false

let pprefix_id id =
  if id == t_lt_float then "Rlt"
  else if id == t_le_float then "Rle"
  else if id == t_gt_float then "Rgt" 
  else if id == t_ge_float then "Rge"
  else assert false

let print_predicate fmt p =
  let rec print0 fmt = function
    | Pif (a, b, c) -> 
	fprintf fmt "(@[if %a@ then %a@ else %a@])"
	  print_term a print0 b print0 c
    | Pimplies (a, b) -> 
	fprintf fmt "(@[%a ->@ %a@])" print1 a print0 b
    | p -> print1 fmt p
  and print1 fmt = function
    | Por (a, b) -> fprintf fmt "%a \\/@ %a" print2 a print1 b
    | p -> print2 fmt p
  and print2 fmt = function
    | Pand (a, b) -> fprintf fmt "%a /\\@ %a" print3 a print2 b
    | p -> print3 fmt p
  and print3 fmt = function
    | Ptrue -> 
	fprintf fmt "True"
    | Pfalse -> 
	fprintf fmt "False"
    | Pvar id -> 
	Ident.print fmt id
    | Papp (id, [a;b]) when id == t_eq ->
	fprintf fmt "@[%a =@ %a@]" print_term a print_term b
    | Papp (id, [a;b]) when id == t_neq ->
	fprintf fmt "~(%a =@ %a)" print_term a print_term b
    | Papp (id, [t]) when id == well_founded ->
	fprintf fmt "@[(well_founded %a)@]" print_term t
    | Papp (id, [a;b]) when id == t_zwf_zero ->
	fprintf fmt "(Zwf `0` %a %a)" print_term a print_term b
    | Papp (id, [a;b]) when is_int_comparison id ->
	openz fmt; 
	fprintf fmt "%a %s@ %a" print_term a (infix_relation id) print_term b; 
	closez fmt
    | Papp (id, [a;b]) when id == t_eq ->
	fprintf fmt "%a = %a" print_term a print_term b
    | Papp (id, [a;b]) when id == t_neq ->
	fprintf fmt "~(%a = %a)" print_term a print_term b
    | Papp (id, [a;b]) when id == t_eq_float ->
	fprintf fmt "(@[eqT R %a %a@])" print_term a print_term b
    | Papp (id, [a;b]) when id == t_neq_float ->
	fprintf fmt "~(@[eqT R %a %a@])" print_term a print_term b
    | Papp (id, [a;b]) when is_float_comparison id ->
	fprintf fmt "(@[%s %a %a@])" (pprefix_id id) print_term a print_term b
    | Papp (id, l) ->
	fprintf fmt "(@[%a %a@])" Ident.print id
	  (print_list space print_term) l
    | Pnot p -> 
	fprintf fmt "~%a" print3 p
    | Forall (id,n,t,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = subst_in_predicate (subst_onev n id') p in
	fprintf fmt "(@[(%s:%a)@ %a@])" (Ident.string id')
	  print_pure_type t print0 p'
    | Exists (id,n,t,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = subst_in_predicate (subst_onev n id') p in
	fprintf fmt "(@[(EX %s:%a |@ %a@])" (Ident.string id')
	  print_pure_type t print0 p'
    | (Por _ | Pand _ | Pif _ | Pimplies _) as p -> 
	fprintf fmt "(%a)" print0 p
  in
  print0 fmt p

let rec print_cc_type fmt = function
  | TTpure pt -> 
      print_pure_type fmt pt
  | TTarray (s, v) -> 
      fprintf fmt "(@[array@ %a@ %a@])" print_term s print_cc_type v
  | TTlambda (b, t) ->
      fprintf fmt "[%a]@,%a" print_binder b print_cc_type t
(*i***
  | TTarrow ((id, CC_var_binder t1), t2) when not (occur_cc_type id t2) -> 
      fprintf fmt "%a -> %a" print_cc_type t1 print_cc_type t2
***i*)
  | TTarrow (b, t) -> 
      fprintf fmt "(%a)@,%a" print_binder b print_cc_type t
  | TTtuple ([_,CC_var_binder t], None) -> 
      print_cc_type fmt t
  | TTtuple (bl, None) ->
      fprintf fmt "(@[tuple_%d@ %a@])" (List.length bl) 
	(print_list space print_binder_type) bl
  | TTtuple (bl, Some q) -> 
      fprintf fmt "(@[sig_%d@ %a@ %a(%a)@])" (List.length bl)
	(print_list space print_binder_type) bl 
	(print_list nothing 
	   (fun fmt b -> fprintf fmt "[%a]@," print_binder b)) bl
	print_cc_type q
  | TTpred p ->
      print_predicate fmt p
  | TTapp (tt, l) ->
      fprintf fmt "(@[%a@ %a@])" print_cc_type tt
	(print_list space print_cc_type) l
  | TTterm t ->
      print_term fmt t

and print_binder fmt (id,b) = 
  Ident.print fmt id;
  match b with
    | CC_pred_binder p -> fprintf fmt ": %a" print_predicate p
    | CC_var_binder t -> fprintf fmt ": %a" print_cc_type t
    | CC_untyped_binder -> ()

and print_binder_type fmt = function
  | _, CC_var_binder t -> print_cc_type fmt t
  | _ -> assert false


let print_sequent fmt (hyps,concl) =
  let rec print_seq = function
    | [] ->
	print_predicate fmt concl
    | Svar (id, v) :: hyps -> 
	fprintf fmt "(%a: @[%a@])@\n" Ident.print id print_cc_type v;
	print_seq hyps
    | Spred (id, p) :: hyps -> 
	fprintf fmt "(%a: @[%a@])@\n" Ident.print id print_predicate p;
	print_seq hyps
  in
  print_seq hyps

let print_proof fmt = function
  | Lemma (s, []) ->
      fprintf fmt "%s" s
  | Lemma (s, vl) ->
      fprintf fmt "@[(%s %a)@]" s (print_list space Ident.print) vl
  | True ->
      fprintf fmt "I"
  | Reflexivity t ->
      fprintf fmt "@[(refl_equal ? %a)@]" print_term t
  | Assumption id -> 
      Ident.print fmt id
  | Proj1 id ->
      fprintf fmt "@[(proj1 ? ? %a)@]" Ident.print id
  | Conjunction (id1, id2) ->
      fprintf fmt "@[(conj ? ? %a %a)@]" Ident.print id1 Ident.print id2

let print_binder_id fmt (id,_) = Ident.print fmt id

let collect_lambdas = 
  let rec collect bl = function
    | CC_lam (b,c) -> collect (b :: bl) c
    | c -> List.rev bl, c
  in
  collect []

let print_lambdas = print_list semi print_binder

let rec collect_app l = function
  | CC_app (e1, e2) -> collect_app (e2 :: l) e1
  | p -> p :: l

let rec print_cc_term fmt = function
  | CC_var id -> 
      Ident.print fmt id
  | CC_lam _ as t ->
      let bl,c = collect_lambdas t in
      fprintf fmt "@[<hov 2>[@[%a@]]@,%a@]" print_lambdas bl print_cc_term c
  | CC_app (f,a) ->
      let tl = collect_app [a] f in
      fprintf fmt "@[<hov 2>(%a)@]" (print_list space print_cc_term) tl
  | CC_tuple (cl, None) ->
      fprintf fmt "(Build_tuple_%d %a)" (List.length cl)
	(print_list space print_cc_term) cl
  | CC_tuple (cl, Some q) ->
      fprintf fmt "(exist_%d %a %a)" (List.length cl - 1)
	print_cc_type q (print_list space print_cc_term) cl
  (* special treatment for the if-then-else *)
  | CC_letin (_, ([idb, CC_var_binder (TTpure PTbool); 
		   qb, CC_pred_binder q] as bl), e1, 
	      CC_if (CC_var idb',
		     CC_lam ((idt, CC_pred_binder _), brt),
		     CC_lam ((idf, CC_pred_binder _), brf)))
    when idb = idb' ->
      fprintf fmt "@[@[<hov 2>let (%a) =@ %a in@]@\n(Cases (@[btest@ [%a:bool]%a@ %a@ %a@]) of@\n| @[<hov 2>(left %a) =>@ %a@]@\n| @[<hov 2>(right %a) =>@ %a@] end)@]"
      (print_list comma print_binder_id) bl print_cc_term e1 
	Ident.print idb print_predicate q Ident.print idb Ident.print qb
	Ident.print idt print_cc_term brt
	Ident.print idf print_cc_term brf
  (* non-dependent boolean if-then-else (probably not of use) *)
  | CC_if (b,e1,e2) ->
      fprintf fmt "@[if "; print_cc_term fmt b; fprintf fmt " then@\n  ";
      hov 0 fmt (print_cc_term fmt) e1;
      fprintf fmt "@\nelse@\n  ";
      hov 0 fmt (print_cc_term fmt) e2;
      fprintf fmt "@]"
  | CC_case (e, pl) ->
      fprintf fmt "@[Cases %a of@\n%a@\nend@]" print_cc_term e
	(print_list newline print_case) pl
  | CC_letin (_,[id,_],c,c1) ->
      fprintf fmt "@[@[<hov 2>let %a =@ %a in@]@\n%a@]"
      Ident.print id print_cc_term c print_cc_term c1
  | CC_letin (_,bl,c,c1) ->
      fprintf fmt "@[@[<hov 2>let (%a) =@ %a in@]@\n%a@]"
      (print_list comma print_binder_id) bl
      print_cc_term c print_cc_term c1
  | CC_term c ->
      fprintf fmt "@["; print_term fmt c; fprintf fmt "@]"
  | CC_hole pr ->
      print_proof fmt pr
  | CC_type t ->
      print_cc_type fmt t

and print_case fmt (p,e) =
  fprintf fmt "@[<hov 2>| %a =>@ %a@]" print_cc_pattern p print_cc_term e

      
let reprint_obligation fmt (id,s) =
  fprintf fmt "@[<hov 2>Lemma %s : @\n%a.@]@\n" id print_sequent s

let print_obligation fmt o = 
  reprint_obligation fmt o;
  fprintf fmt "Proof.@\n";
  option_iter (fun t -> fprintf fmt "%s.@\n" t) coq_tactic;
  fprintf fmt "(* FILL PROOF HERE *)@\nSave.@\n"

let reprint_validation fmt id v =
  fprintf fmt "@[Definition %s := (* validation *)@\n  %a.@]@\n" 
    id print_cc_term v

let print_validation = reprint_validation

let reprint_parameter fmt id c =
  fprintf fmt 
    "@[<hov 2>(*Why*) Parameter %s :@ @[%a@].@]@\n" id print_cc_type c

let print_parameter = reprint_parameter

(*s Elements to produce. *)

type element_kind = 
  | Param
  | Oblig
  | Valid

type element_id = element_kind * string

type element = 
  | Parameter of string * cc_type
  | Obligation of obligation
  | Validation of string * validation

let elem_t = Hashtbl.create 97 (* maps [element_id] to [element] *)
let elem_q = Queue.create ()   (* queue of [element_id * element] *)

let add_elem ek e = Queue.add (ek,e) elem_q; Hashtbl.add elem_t ek e

let reset () = Queue.clear elem_q; Hashtbl.clear elem_t

let push_obligations = 
  List.iter (fun ((l,_) as o) -> add_elem (Oblig, l) (Obligation o))

let push_validation id v = 
  add_elem (Valid, id) (Validation (id,v))

let push_parameter id v =
  add_elem (Param, id) (Parameter (id,v))

let print_element_kind fmt = function
  | Param, s -> fprintf fmt "parameter %s" s
  | Oblig, s -> fprintf fmt "obligation %s" s
  | Valid, s -> fprintf fmt "validation %s" s

let print_element fmt e = 
  begin match e with
    | Parameter (id, c) -> print_parameter fmt id c
    | Obligation o -> print_obligation fmt o
    | Validation (id, v) -> print_validation fmt id v
  end;
  fprintf fmt "@\n"

let reprint_element fmt = function
  | Parameter (id, c) -> reprint_parameter fmt id c
  | Obligation o -> reprint_obligation fmt o
  | Validation (id, v) -> reprint_validation fmt id v

(*s Generating the output. *)

let regexps = ref []

let add_regexp r k = regexps := (Str.regexp r, k) :: !regexps

let _ = 
  add_regexp 
    "Lemma[ ]+\\(.*_po_[0-9]+\\)[ ]*:[ ]*" Oblig;
  add_regexp 
    "Definition[ ]+\\([^ ]*\\)[ ]*:=[ ]*(\\* validation \\*)[ ]*" Valid;
  add_regexp 
    "(\\*Why\\*) Parameter[ ]+\\([^ ]*\\)[ ]*:[ ]*" Param

let check_line s =
  let rec test = function
    | [] -> 
	None
    | (r, k) :: l ->
	if Str.string_match r s 0 then 
	  Some (k, Str.matched_group 1 s) 
	else 
	  test l
  in
  test !regexps

let end_is_not_dot s =
  let n = String.length s in n = 0 || s.[n-1] <> '.'

let regen oldf fmt =
  let cin = open_in oldf in
  let rec scan () =
    let s = input_line cin in
    match check_line s with
      | None -> 
	  fprintf fmt "%s@\n" s;
	  scan ()
      | Some e ->
	  if Hashtbl.mem elem_t e then begin
	    if verbose then eprintf "overwriting %a@." print_element_kind e;
	    print_up_to e
	  end else
	    if verbose then eprintf "erasing %a@." print_element_kind e;
	  if end_is_not_dot s then skip_to_dot ();
	  scan ()
  and skip_to_dot () =
    let s = input_line cin in
    if end_is_not_dot s then skip_to_dot ()
  and tail () = 
    fprintf fmt "%c" (input_char cin); tail () 
  and print_up_to e =
    let (e',ee) = Queue.take elem_q in
    Hashtbl.remove elem_t e'; 
    if e = e' then 
      reprint_element fmt ee 
    else begin
      print_element fmt ee; print_up_to e
    end
  in
  begin
    try scan () with End_of_file -> 
    try tail () with End_of_file -> close_in cin
  end;
  Queue.iter (fun (_,e) -> print_element fmt e) elem_q

let first_time fmt =
  fprintf fmt "\
(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)@\n
Require Why.@\n@\n";
  Queue.iter (fun (_,e) -> print_element fmt e) elem_q

let print_in_file p f =
  let cout = open_out f in
  let fmt = formatter_of_out_channel cout in
  p fmt;
  pp_print_flush fmt ();
  close_out cout

let output_file fwe =
  let f = fwe ^ "_why.v" in
  if Sys.file_exists f then begin
    let fbak = f ^ ".bak" in
    Sys.rename f fbak; 
    if_verbose_3 eprintf "*** re-generating file %s (backup in %s)@." f fbak;
    print_in_file (regen fbak) f
  end else begin
    if_verbose_2 eprintf "*** generating file %s@." f;
    print_in_file first_time f
  end
