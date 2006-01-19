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

(*i $Id: smtlib.ml,v 1.7 2006-01-19 14:17:04 filliatr Exp $ i*)

(*s Harvey's output *)

open Ident
open Options
open Misc
open Error
open Logic
open Cc
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
      fprintf fmt "%s" n
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

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "Int"
  | PTbool -> fprintf fmt "Bool"
  | PTreal -> fprintf fmt "Real"
  | PTunit -> fprintf fmt "Unit"
  | PTexternal(_,id) when id==farray -> fprintf fmt "Array" 
  | PTvar {type_val=Some pt} -> print_pure_type fmt pt
  | PTvar _ -> assert false
  | PTexternal (i,id) -> fprintf fmt "%a%a" Ident.print id instance i

and instance fmt = function
  | [] -> ()
  | ptl -> fprintf fmt "_%a" (print_list underscore print_pure_type) ptl


let rec print_predicate fmt = function
  | Ptrue ->
      fprintf fmt "true"
  | Pvar id when id == Ident.default_post ->
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
      fprintf fmt "@[(implies@ %a@ %a)@]" print_predicate a print_predicate b
  | Pif (a, b, c) ->
      fprintf fmt "@[(ite@ %a@ %a@ %a)@]" print_term a print_predicate b
	print_predicate c
  | Pand (_, _, a, b) | Forallb (_, a, b) ->
      fprintf fmt "@[(and@ %a@ %a)@]" print_predicate a print_predicate b
  | Por (a, b) ->
      fprintf fmt "@[(or@ %a@ %a)@]" print_predicate a print_predicate b
  | Piff (a, b) ->
      fprintf fmt "@[(iff@ %a@ %a)@]" print_predicate a print_predicate b
  | Pnot a ->
      fprintf fmt "@[(not@ %a)@]" print_predicate a
  | Forall (_,id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(forall (%a %a) %a)@]" 
	Ident.print id' print_pure_type t print_predicate p'
  | Exists (id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(exists (%a %a) %a)@]" Ident.print id' print_pure_type t print_predicate p'
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
  fprintf fmt "@[(forall %a (iff (%s %a)@ @[%a@]))@]@\n@\n" 
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

let external_type = function
  | PTexternal _ -> true
  | _ -> false

let cc_external_type = function
  | Cc.TTpure ty -> external_type ty
  | Cc.TTarray (Cc.TTpure (PTexternal _)) -> true
  | _ -> false

let rec print_cc_type fmt = function
  | Cc.TTpure pt -> 
      print_pure_type fmt pt
  | Cc.TTarray v -> 
      fprintf fmt "@[Array@]" 
  | Cc.TTarrow ((_,Cc.CC_var_binder t1), t2) -> 
      fprintf fmt "[%a ->@ %a]" print_cc_type t1 print_cc_type t2
  | _ -> 
      assert false

let output_sequent fmt (hyps,concl) =
  let rec print_seq fmt = function
    | [] ->
	print_predicate fmt concl
    | Svar (id, v) :: hyps -> 
	fprintf fmt "@[(forall (%a %a)@ %a)@]" 
	  Ident.print id print_cc_type v print_seq hyps
    | Spred (_,p) :: hyps -> 
	fprintf fmt "@[(implies@ %a@ %a)@]" print_predicate p print_seq hyps
  in
  print_seq fmt hyps


(*s First-order checks *)


let rec filter_context = function
  | [] -> []
  | Svar (id, _) :: ctx -> filter_context ctx
  | Spred (_, p) :: ctx -> p :: filter_context ctx

exception NotFirstOrder

let output_obligation fmt (loc, o, s) = 
  try
    fprintf fmt "\n  :formula"; 
    fprintf fmt "@[;; %a@]@\n" Loc.report_obligation_position loc;
    output_sequent fmt s;
    fprintf fmt "\n\n" 
  with NotFirstOrder ->
    unlocated_wprintf "obligation %s is not first-order@\n" o

let output_file f = 
  let fname = f ^ "_why.smt" in
  let cout = open_out fname in
  let fmt = formatter_of_out_channel cout in

  fprintf fmt "(benchmark %s\n" f;
  fprintf fmt "  :source { Generated by the Caduceus tool ... \n";
  fprintf fmt "            MORE ON Caduceus AND Why...       }\n";
  fprintf fmt "  :status unknown\n";
  fprintf fmt "  :logic  caduceus_logic\n";

  Queue.iter (output_obligation fmt) oblig;
  fprintf fmt "\n)\n";
  pp_print_flush fmt ();
  close_out cout

