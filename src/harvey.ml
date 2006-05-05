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

(*i $Id: harvey.ml,v 1.38 2006-05-05 14:42:55 filliatr Exp $ i*)

(*s Harvey's output *)

open Ident
open Misc
open Error
open Logic
open Logic_decl
open Cc
open Format
open Pp

type elem = 
  | Axiom of string * predicate Env.scheme
  | Predicate of string * predicate_def Env.scheme
  | FunctionDef of string * function_def Env.scheme

let theory = Queue.create ()
let oblig = Queue.create ()

let reset () = Queue.clear theory; Queue.clear oblig

let push_decl = function
  | Dgoal (loc,id,s) -> Queue.add (loc,id,s.Env.scheme_type) oblig
  | Daxiom (_, id, p) -> Queue.add (Axiom (id, p)) theory
  | Dpredicate_def (_, id, p) -> Queue.add (Predicate (id, p)) theory
  | Dfunction_def (_, id, p) -> Queue.add (FunctionDef (id, p)) theory
  | Dtype _ -> ()
  | Dlogic _ -> ()

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

(* we need to rename a few identifiers *)

let is_harvey_keyword =
  let ht = Hashtbl.create 17 in
  List.iter (fun kw -> Hashtbl.add ht kw ()) 
    ["true"; "false"; "le"; "lt"];
  Hashtbl.mem ht

let is_harvey_ident s =
  let is_harvey_char = function
    | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> true 
    | _ -> false
  in
  let is_harvey_first_char = function
    | 'a'..'z' | 'A'..'Z' | '0'..'9' -> true 
    | _ -> false
  in
  String.length s > 0 && is_harvey_first_char s.[0] &&
  (try 
     String.iter (fun c -> if not (is_harvey_char c) then raise Exit) s; true
   with Exit ->
     false)

let renamings = Hashtbl.create 17
let fresh_name = 
  let r = ref 0 in fun () -> incr r; "harvey__" ^ string_of_int !r

let ident fmt id =
  let s = Ident.string id in
  if is_harvey_keyword s then
    fprintf fmt "harvey__%s" s
  else if not (is_harvey_ident s) then 
    let s' = 
      try
	Hashtbl.find renamings s
      with Not_found ->
	let s' = fresh_name () in
	Hashtbl.add renamings s s';
	s'
    in
    fprintf fmt "%s" s'
  else
    Ident.print fmt id

let rec print_term fmt = function
  | Tvar id | Tapp (id, [], _) -> 
      fprintf fmt "%a" ident id
  | Tconst (ConstInt n) -> 
      fprintf fmt "%s" n
  | Tconst (ConstBool b) -> 
      fprintf fmt "harvey__%b" b
  | Tconst ConstUnit -> 
      fprintf fmt "tt" 
  | Tconst (ConstFloat _) ->
      Report.raise_unlocated (AnyMessage "haRVey does not support reals")
  | Tderef _ -> 
      assert false
  | Tapp (id, [a; b; c], _) when id == if_then_else -> 
      fprintf fmt "@[(why__ite@ %a@ %a@ %a)@]" print_term a print_term b
	print_term c
  | Tapp (id, [a], _) when id == t_neg_int ->
      fprintf fmt "@[(- 0 %a)@]" print_term a
  | Tapp (id, tl, _) when is_relation id || is_arith id ->
      fprintf fmt "@[(%s %a)@]" (prefix id) print_terms tl
  | Tapp (id, tl, _) ->
      fprintf fmt "@[(%a@ %a)@]" 
	ident id (print_list space print_term) tl

and print_terms fmt tl = 
  print_list space print_term fmt tl

let rec print_predicate fmt = function
  | Ptrue ->
      fprintf fmt "true"
  | Pvar id when id == Ident.default_post ->
      fprintf fmt "true"
  | Pfalse ->
      fprintf fmt "false"
  | Pvar id -> 
      fprintf fmt "%a" ident id
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
      fprintf fmt "@[(%a@ %a)@]" ident id print_terms tl
  | Pimplies (_, a, b) ->
      fprintf fmt "@[(->@ %a@ %a)@]" print_predicate a print_predicate b
  | Pif (a, b, c) ->
      fprintf fmt "@[(ite@ %a@ %a@ %a)@]" print_term a print_predicate b
	print_predicate c
  | Pand (_, _, a, b) | Forallb (_, a, b) ->
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
      fprintf fmt "@[(forall %a@ %a)@]" ident id' print_predicate p'
  | Exists (id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(exists %a@ %a)@]" ident id' print_predicate p'
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
  fprintf fmt "@[;; Why predicate %s@\n" id;
  fprintf fmt "@[(forall %a@ @[(<-> (%s %a)@ @[%a@])@])@]@]@\n@\n" 
    (print_list space (fun fmt (x,_) -> ident fmt x)) bl id
    (print_list space (fun fmt (x,_) -> ident fmt x)) bl 
    print_predicate p

let print_function_def fmt id p =
  let (bl,_,e) = p.Env.scheme_type in
  fprintf fmt "@[;; Why function %s@\n" id;
  fprintf fmt "@[(forall %a@ @[(= (%s %a)@ @[%a@])@])@]@]@\n@\n" 
    (print_list space (fun fmt (x,_) -> ident fmt x)) bl id
    (print_list space (fun fmt (x,_) -> ident fmt x)) bl 
    print_term e

let print_elem fmt = function
  | Axiom (id, p) -> print_axiom fmt id p
  | Predicate (id, p) -> print_predicate_def fmt id p
  | FunctionDef (id, f) -> print_function_def fmt id f

let output_theory fmt f =
  fprintf fmt "(@\n@[";
  fprintf fmt "(theory %s_why@\n(extends)@\n(axioms@\n" f;
  Queue.iter (print_elem fmt) theory;
  fprintf fmt "))@\n";
  fprintf fmt "@]@\n) ;; END THEORY@\n"

let output_sequent fmt (ctx, concl) = 
  let rec print_seq fmt = function
    | [] -> 
	fprintf fmt "@[%a@]" print_predicate concl
    | Svar (id, ty) :: ctx -> 
	fprintf fmt "@[(forall %a@ %a)@]"
	  Ident.print id print_seq ctx
    | Spred (_, p) :: ctx -> 
	fprintf fmt "@[<hov 2>(->@ @[%a@]@ %a)@]" 
	  print_predicate p print_seq ctx
  in
  print_seq fmt ctx

let output_obligation fmt (loc, o, s) = 
  fprintf fmt "@\n@[;; %a@]@\n" Loc.report_obligation_position loc;
  fprintf fmt "@[%a@]@\n" output_sequent s

let output_file f = 
  let fname = Options.out_file (f ^ "_why.rv") in
  let cout = open_out fname in
  let fmt = formatter_of_out_channel cout in
  if Options.no_harvey_prelude then 
    fprintf fmt "()@\n" 
  else 
    output_theory fmt (Filename.basename f);
  Queue.iter (output_obligation fmt) oblig;
  pp_print_flush fmt ();
  close_out cout

