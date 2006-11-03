(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

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

(*i $Id: gappa.ml,v 1.9 2006-11-03 11:55:29 marche Exp $ i*)

(*s Gappa's output *)

open Ident
open Options
open Misc
open Error
open Logic
open Cc
open Format
open Pp

(* Gappa terms and formulas *)

type exact = Exact | Float

type gterm =
  | Gvar of exact * string
  | Grnd of gterm
  | Gcst of real_constant
  | Gneg of gterm
  | Gadd of gterm * gterm
  | Gsub of gterm * gterm
  | Gmul of gterm * gterm
  | Gdiv of gterm * gterm

type gpred =
  | Gin of gterm * real_constant * real_constant
  | Gimplies of gpred * gpred
  | Gand of gpred * gpred
  | Gnot of gpred

type gobligation = (string * gterm) list * gpred

(* compilation to Gappa formulas *)

let t_float = Ident.create "float"
let neg_float = Ident.create "neg_float"
let add_float = Ident.create "add_float"
let sub_float = Ident.create "sub_float"
let mul_float = Ident.create "mul_float"
let div_float = Ident.create "div_float"
let float_part = Ident.create "float_part"
let real_part = Ident.create "real_part"
let id_rnd = Ident.create "rnd"

let rnd e = if e = Exact then (fun t -> t) else (fun t -> Grnd t)

let rec term e = function
  | Tconst (ConstFloat f) -> 
      Gcst f
  | Tconst _ ->
      assert false (*TODO*)
  | Tvar id -> 
      Gvar (e, Ident.string id)
  | Tderef id -> 
      Gvar (e, Ident.string id)
  (* real ops *)
  | Tapp (id, [t], _) when id == t_neg_real -> 
      Gneg (term e t)
  | Tapp (id, [t1; t2], _) when id == t_add_real -> 
      Gadd (term e t1, term e t2)
  | Tapp (id, [t1; t2], _) when id == t_sub_real -> 
      Gsub (term e t1, term e t2)
  | Tapp (id, [t1; t2], _) when id == t_mul_real -> 
      Gmul (term e t1, term e t2)
  | Tapp (id, [t1; t2], _) when id == t_div_real -> 
      Gdiv (term e t1, term e t2)
  (* float ops *)
  | Tapp (id, [t], _) when id == neg_float -> 
      rnd e (Gneg (term e t))
  | Tapp (id, [t1; t2], _) when id == add_float -> 
      rnd e (Gadd (term e t1, term e t2))
  | Tapp (id, [t1; t2], _) when id == sub_float -> 
      rnd e (Gsub (term e t1, term e t2))
  | Tapp (id, [t1; t2], _) when id == mul_float -> 
      rnd e (Gmul (term e t1, term e t2))
  | Tapp (id, [t1; t2], _) when id == div_float -> 
      rnd e (Gdiv (term e t1, term e t2))
  | Tapp (id, [t], _) when id == id_rnd ->
      Grnd (term Exact t)
  (* anything else is abstracted *)
  | Tapp (id, [t], _) when id == float_part ->
      term Float t
  | Tapp (id, [t], _) when id == real_part ->
      term Exact t
  | Tapp _ -> 
      assert false (*TODO: abstract*)

(* recognition of a predicate as a conjunction (a list) of Gappa predicates *)

type gappa_pred = 
  | Equation of (string * gterm)
  | Interval of (gterm * real_constant * real_constant)
  | Other of predicate

let rec gpred = function
  | Papp (id, [Tvar x; t2], _) when is_eq id ->
      [Equation (Ident.string x, term Float t2)]
  | Pand (_, _, 
	  Papp (id1, [Tconst (ConstFloat f1); t1], _),
	  Papp (id2, [t2; Tconst (ConstFloat f2)], _))
    when id1 == t_le_real && id2 == t_le_real && t1 = t2 ->
      [Interval (term Float t1, f1, f2)]
  | Pand (_, _, p1, p2) ->
      gpred p1 @ gpred p2
  | Pnamed (_, p) ->
      gpred p
  | Pimplies _ | Forall _ as p -> (* saved for later intros *)
      [Other p]
  | Papp _
  | Por _
  | Pif _
  | Piff _
  | Pnot _
  | Forallb _
  | Exists _
  | Pfpi _
  | Ptrue | Pfalse | Pvar _ -> (* discarded *)
      [] 

let fresh_var = 
  let r = ref 0 in fun () -> incr r; "gappa_" ^ string_of_int !r

(* splits the context into two lists: one list of equations and one list of
   assumed intervals *)
let context ctx = 
  let rec split eqs ins = function
    | [] ->
	eqs, ins
    | Svar (x, PTexternal (_, id)) :: l when id == t_float ->
	let v = fresh_var () in
	let e = Ident.string x, Grnd (Gvar (Float, v)) in
	split (e :: eqs) ins l
    | Svar _ :: l ->
	split eqs ins l
    | Spred (_, p) :: l ->
	let eqs, ins = 
	  List.fold_left
	    (fun (eqs,ins) p -> match p with
	       | Equation e -> e::eqs, ins
	       | Interval i -> eqs, i :: ins
	       | Other _ -> eqs, ins)
	    (eqs, ins) (gpred p)
	in
	split eqs ins l
  in
  split [] [] ctx

(* Processing obligations.
   One Why obligation can be split into several Gappa obligations *)

let queue = Queue.create ()

let reset () = Queue.clear queue

let add_ctx_vars =
  List.fold_left 
    (fun acc -> function Svar (id,_) -> Idset.add id acc | _ -> acc)

let rec intros ctx = function
  | Forall (true, id, n, t, _, p) ->
      (*let id' = next_away id (predicate_vars p) in*)
      let id' = next_away id (add_ctx_vars (predicate_vars p) ctx) in
      let p' = subst_in_predicate (subst_onev n id') p in
      intros (Svar (id', t) :: ctx) p'
  | Pimplies (true, a, b) -> 
      let h = fresh_hyp () in 
      intros (Spred (h, a) :: ctx) b
  | Pnamed (_, p) ->
      intros ctx p
  | c -> 
      ctx, c

let process_obligation (ctx, concl) =
  let rec process ctx concl =
    let ctx,concl = intros ctx concl in
    List.iter (process_one ctx) (gpred concl)
  and process_one ctx = function
    | Equation _-> 
	()
    | Interval (t,f1,f2) ->
	let concl = Gin (t,f1,f2) in
	let eqs,ins = context ctx in
	let concl = match ins with
	  | [] -> 
	      concl
	  | (t,f1,f2) :: ins ->  
	      let p = Gin (t,f1,f2) in
	      let p =
		List.fold_right 
		  (fun (t,f1,f2) p -> Gand (Gin (t,f1,f2), p)) ins p
	      in
	      Gimplies (p, concl)
	in 
	Queue.add (eqs, concl) queue
    | Other p ->
	process ctx p
  in
  process ctx concl

let push_decl = function
  | Logic_decl.Dgoal (_,_,s) -> process_obligation s.Env.scheme_type
  | _ -> ()

let print_real fmt = function
  | (i,f,"") -> fprintf fmt "%s.%s" i f
  | (i,f,e) -> fprintf fmt "%s.%se%s" i f e

let rec print_term fmt = function
  | Gvar (Float, x) -> fprintf fmt "%s" x
  | Gvar (Exact, x) -> fprintf fmt "exact_%s" x
  | Grnd t -> fprintf fmt "rnd(%a)" print_term t
  | Gcst r -> print_real fmt r
  | Gneg t -> fprintf fmt "(-%a)" print_term t
  | Gadd (t1, t2) -> fprintf fmt "(%a + %a)" print_term t1 print_term t2
  | Gsub (t1, t2) -> fprintf fmt "(%a - %a)" print_term t1 print_term t2
  | Gmul (t1, t2) -> fprintf fmt "(%a * %a)" print_term t1 print_term t2
  | Gdiv (t1, t2) -> fprintf fmt "(%a / %a)" print_term t1 print_term t2

let rec print_pred fmt = function
  | Gin (t, r1, r2) ->
      fprintf fmt "%a in [%a, %a]" print_term t print_real r1 print_real r2
  | Gimplies (p1, p2) ->
      fprintf fmt "(%a ->@ %a)" print_pred p1 print_pred p2
  | Gand (p1, p2) ->
      fprintf fmt "(%a and %a)" print_pred p1 print_pred p2
  | Gnot p ->
      fprintf fmt "(not %a)" print_pred p

let print_equation fmt (x, t) = 
  fprintf fmt "@[%s = %a;@]@\n" x print_term t

let print_obligation fmt (eq,p) =
  fprintf fmt "@@rnd = %s;@\n@\n" gappa_rnd;
  fprintf fmt "%a@\n" (print_list newline print_equation) eq;
  fprintf fmt "@[{ %a }@]@." print_pred p

let output_file fwe =
  let sep = "### DO NOT EDIT ABOVE THIS LINE" in
  let i = ref 0 in
  Queue.iter
    (fun o ->
       incr i;
       if debug then eprintf "gappa obligation %d@." !i;
       let file = fwe ^ "_why" ^ "_po_" ^ string_of_int !i ^ ".gappa" in
       do_not_edit_above ~file
	 ~before:(fun fmt -> print_obligation fmt o)
	 ~sep
	 ~after:(fun fmt -> ()))
    queue


