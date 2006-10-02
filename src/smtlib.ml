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

(*i $Id: smtlib.ml,v 1.19 2006-10-02 09:08:38 couchot Exp $ i*)

(*s Harvey's output *)

open Ident
open Options
open Misc
open Error
open Logic
open Logic_decl
open Env
open Cc
open Format
open Pp

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
       || id == t_lt_real
       || id == t_le_real
       || id == t_gt_real
       || id == t_ge_real
  then
    Ident.string id
  else (eprintf "%a@." Ident.print id; assert false)

let print_bvar fmt id = fprintf fmt "?%a" Ident.print id

let is_smtlib_keyword =
  let ht = Hashtbl.create 50  in
  List.iter (fun kw -> Hashtbl.add ht kw ()) 
    ["and";" benchmark";" distinct";"exists";"false";"flet";"forall";
     "if then else";"iff";"implies";"ite";"let";"logic";"not";"or";
     "sat";"theory";"true";"unknown";"unsat";"xor";
     "assumption";"axioms";"defintion";"extensions";"formula";
     "funs";"extrafuns";"extrasorts";"extrapreds";"language";
     "notes";"preds";"sorts";"status";"theory";"Int";"Real";"Bool"];
  Hashtbl.mem ht

let idents fmt s = 
  if is_smtlib_keyword s then
    fprintf fmt "smtlib__%s" s
  else 
    fprintf fmt "%s" s

let ident fmt id = idents fmt (Ident.string id)

let rec print_term fmt = function
  | Tvar id -> 
      print_bvar fmt id
  | Tconst (ConstInt n) -> 
      fprintf fmt "%s" n
  | Tconst (ConstBool b) -> 
      fprintf fmt "Boolean_%b" b
  | Tconst ConstUnit -> 
      fprintf fmt "tt" 
  | Tconst (ConstFloat (i,f,e)) ->
      fprintf fmt "%s.%s" i f ;
      if not (e = "") then
	failwith "exposant notation not yet suported "
  | Tderef _ -> 
      assert false
  | Tapp (id, [a; b; c], _) when id == if_then_else -> 
      fprintf fmt "@[(ite@ (= %a Boolean_true) @ %a@ %a)@]" 
	print_term a print_term b print_term c
  | Tapp (id, tl, _) when is_relation id || is_arith id ->
      fprintf fmt "@[(%s %a)@]" (prefix id) print_terms tl
  | Tapp (id, [], i) -> 
      fprintf fmt "%a" idents (Encoding.symbol (id, i))
  | Tapp (id, tl, i) ->
      fprintf fmt "@[(%a@ %a)@]" 
	idents (Encoding.symbol (id, i)) (print_list space print_term) tl

and print_terms fmt tl = 
  print_list space print_term fmt tl

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "Int"
  | PTbool -> fprintf fmt "Boolean"
  | PTreal -> fprintf fmt "Real"
  | PTunit -> fprintf fmt "Unit"
  | PTexternal(_,id) when id==farray -> fprintf fmt "Array" 
  | PTvar {type_val=Some pt} -> print_pure_type fmt pt
  | PTvar v -> assert false (*  fprintf fmt "A%d" v.tag *)
  | PTexternal (i,id) -> idents fmt (Encoding.symbol (id, i))

and instance fmt = function
  | [] -> ()
  | ptl -> fprintf fmt "_%a" (print_list underscore print_pure_type) ptl

let bound_variable =
  let x = ref 0 in
  fun () -> incr x; Ident.create ("bv" ^ string_of_int !x)

let rec print_predicate fmt = function
  | Ptrue ->
      fprintf fmt "true"
  | Pvar id when id == Ident.default_post ->
      fprintf fmt "true"
  | Pfalse ->
      fprintf fmt "false"
  | Pvar id -> 
      fprintf fmt "%a" ident id
  | Papp (id, [t], _) when id == well_founded ->
      fprintf fmt "true;; was well founded @\n" 
  | Papp (id, [a; b], _) when is_eq id ->
      fprintf fmt "@[(= %a@ %a)@]" print_term a print_term b
  | Papp (id, [a; b], _) when is_neq id ->
      fprintf fmt "@[(not (= %a@ %a))@]" print_term a print_term b
  | Papp (id, tl, _) when is_relation id || is_arith id ->
      fprintf fmt "@[(%s %a)@]" (prefix id) print_terms tl
  | Papp (id, [a;b], _) when id == t_zwf_zero ->
      fprintf fmt "@[(and (<= 0 %a)@ (< %a %a))@]" 
	print_term b print_term a print_term b
  | Papp (id, tl, i) -> 
      fprintf fmt "@[(%a@ %a)@]" 
	idents (Encoding.symbol (id, i)) print_terms tl
  | Pimplies (_, a, b) ->
      fprintf fmt "@[(implies@ %a@ %a)@]" print_predicate a print_predicate b
  | Pif (a, b, c) ->
      fprintf fmt "@[(if_then_else@ (= %a Boolean_true)@ %a@ %a)@]" 
	print_term a print_predicate b print_predicate c
  | Pand (_, _, a, b) | Forallb (_, a, b) ->
      fprintf fmt "@[(and@ %a@ %a)@]" print_predicate a print_predicate b
  | Por (a, b) ->
      fprintf fmt "@[(or@ %a@ %a)@]" print_predicate a print_predicate b
  | Piff (a, b) ->
      fprintf fmt "@[(iff@ %a@ %a)@]" print_predicate a print_predicate b
  | Pnot a ->
      fprintf fmt "@[(not@ %a)@]" print_predicate a
  | Forall (_,id,n,t,_,p) -> 
      (*let id' = next_away id (predicate_vars p) in*)
      let id' = bound_variable () in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(forall (%a %a)@ %a)@]" 
	print_bvar id' print_pure_type t print_predicate p'
  | Exists (id,n,t,p) -> 
      (*let id' = next_away id (predicate_vars p) in*)
      let id' = bound_variable () in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(exists (%a %a) %a)@]" 
	print_bvar id' print_pure_type t print_predicate p'
  | Pfpi _ ->
      failwith "fpi not supported with haRVey"
  | Pnamed (_, p) -> (* TODO: print name *)
      print_predicate fmt p

let print_axiom fmt id p =
  fprintf fmt "@[;; Why axiom %s@]@\n" id;
  fprintf fmt " @[<hov 2>:assumption@ %a@]" print_predicate p;
  fprintf fmt "@]@\n@\n" 

let print_quantifiers =
  let print_quantifier fmt (x,t) = 
    fprintf fmt "(%a %a)" print_bvar x print_pure_type t
  in
  print_list space print_quantifier 

let pure_type_list = print_list space print_pure_type

let print_predicate_def fmt id (bl,p) =
  let tl = List.map snd bl in
  fprintf fmt "@[:extrapreds ((%a %a))@]@\n@\n" idents id pure_type_list tl;
  fprintf fmt "@[:assumption@ (forall %a@ (iff (%a %a)@ @[%a@]))@]@\n@\n" 
    print_quantifiers bl idents id
    (print_list space (fun fmt (x,_) -> print_bvar fmt x)) bl 
    print_predicate p

let print_function_def fmt id (bl,pt,e) =
  let tl = List.map snd bl in
  fprintf fmt "@[:extrafuns ((%a %a %a))@]@\n@\n" idents id pure_type_list tl
    print_pure_type pt;
  fprintf fmt "@[:assumption@ (forall %a@ (= (%a %a)@ @[%a@]))@]@\n@\n" 
    print_quantifiers bl 
    idents 
    id
    (print_list space (fun fmt (x,_) -> print_bvar fmt x)) bl 
    print_term e

let output_sequent fmt (hyps,concl) =
  let rec print_seq fmt = function
    | [] ->
	print_predicate fmt concl
    | Svar (id, v) :: hyps -> 
	fprintf fmt "@[(forall (%a %a)@ %a)@]" 
	  print_bvar id print_pure_type v print_seq hyps
(* TODO : update this for renaming each variable *) 
    | Spred (_,p) :: hyps -> 
	fprintf fmt "@[(implies@ %a@ %a)@]" print_predicate p print_seq hyps
  in
  print_seq fmt hyps

let print_obligation fmt loc o s = 
  fprintf fmt "@[:formula@\n"; 
  fprintf fmt "  @[;; %a@]@\n" Loc.report_obligation_position loc;
  fprintf fmt "  @[(not@ %a)@]" output_sequent s;
  fprintf fmt "@]@\n@\n" 

let push_decl d = Encoding.push d

let iter = Encoding.iter

let reset () = Encoding.reset ()

let declare_type fmt id =
  fprintf fmt ":extrasorts (%s)@\n" id

let print_logic fmt id t =
  fprintf fmt ";;;; Why logic %s@\n" id;
  match t with
    | Predicate tl ->
	fprintf fmt "@[:extrapreds ((%a %a))@]@\n@\n" 
	  idents id pure_type_list tl
    | Function (tl, pt) ->
	fprintf fmt "@[:extrafuns ((%a %a %a))@]@\n@\n" 
	  idents id pure_type_list tl print_pure_type pt
	
let output_elem fmt = function
  | Dtype (loc, [], id) -> declare_type fmt id
  | Dtype (_, _, id) -> fprintf fmt ";; polymorphic type %s@\n@\n" id
  | Dlogic (loc, id, t) -> print_logic fmt id t.scheme_type
  | Dpredicate_def (loc, id, d) -> print_predicate_def fmt id d.scheme_type
  | Dfunction_def (loc, id, d) -> print_function_def fmt id d.scheme_type
  | Daxiom (loc, id, p) -> print_axiom fmt id p.scheme_type
  | Dgoal (loc, id, s) -> print_obligation fmt loc id s.Env.scheme_type



let output_file f = 
  let fname = f ^ "_why.smt" in
  let cout = open_out fname in
  let fmt = formatter_of_out_channel cout in
  fprintf fmt "(benchmark %a@\n" idents (Filename.basename f);
  (*fprintf fmt "  :source { Generated by the Why tool }@\n";*)
  fprintf fmt "  :status unknown@\n";
  (*fprintf fmt "  :logic  caduceus_logic\n";*)
  fprintf fmt "  :extrasorts (Boolean)@\n";
  fprintf fmt "  :extrasorts (Unit)@\n";
  fprintf fmt "  :extrafuns ((Boolean_true Boolean))@\n";
  fprintf fmt "  :extrafuns ((Boolean_false Boolean))@\n";
  fprintf fmt "  :assumption
                   (forall (?bcd Boolean) (or (= ?bcd Boolean_true) 
                                            (= ?bcd Boolean_false)))@\n";
  fprintf fmt "  :extrafuns ((int_div Int Int Int))@\n";
  fprintf fmt "  :extrafuns ((int_mod Int Int Int))@\n";
  
 (** if the pruning option is selected. May be the normal flow **)
  iter (output_elem fmt);
  (* end of smtlib file *)
  fprintf fmt "@\n)@\n";
  pp_print_flush fmt ();
  close_out cout

(** this method aims at replacing the above one.
    Compare to it, it takes as input the queue of reduced theory
**)
let output_file_reduced f q = 
  let fname = f ^ "_why.smt" in
  let cout = open_out fname in
  let fmt = formatter_of_out_channel cout in
  fprintf fmt "(benchmark %s@\n" (Filename.basename f);
  (*fprintf fmt "  :source { Generated by the Why tool }@\n";*)
  fprintf fmt "  :status unknown@\n";
  (*fprintf fmt "  :logic  caduceus_logic\n";*)
  fprintf fmt "  :extrasorts (Boolean)@\n";
  fprintf fmt "  :extrasorts (Unit)@\n";
  fprintf fmt "  :extrafuns ((Boolean_true Boolean))@\n";
  fprintf fmt "  :extrafuns ((Boolean_false Boolean))@\n";
  fprintf fmt "  :assumption
                   (forall (?bcd Boolean) (or (= ?bcd Boolean_true) 
                                            (= ?bcd Boolean_false)))@\n";
  fprintf fmt "  :extrafuns ((int_div Int Int Int))@\n";
  fprintf fmt "  :extrafuns ((int_mod Int Int Int))@\n";
  
 (** if the pruning option is selected. May be the normal flow **)
    
  Queue.iter (fun v  -> output_elem fmt v) q;
  fprintf fmt "@\n)@\n";
  pp_print_flush fmt ();
  close_out cout
