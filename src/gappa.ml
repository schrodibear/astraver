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

(*i $Id: gappa.ml,v 1.1 2006-02-03 15:35:49 filliatr Exp $ i*)

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

type gterm =
  | Gvar of string
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

let neg_float = Ident.create "neg_float"
let add_float = Ident.create "add_float"
let sub_float = Ident.create "sub_float"
let mul_float = Ident.create "mul_float"
let div_float = Ident.create "div_float"

let rec term = function
  | Tconst (ConstFloat f) -> 
      Gcst f
  | Tconst _ ->
      assert false (*TODO*)
  | Tvar id -> 
      assert false (*TODO*)
  | Tderef id -> 
      assert false (*TODO*)
  (* real ops *)
  | Tapp (id, [t], _) when id == t_neg_real -> 
      Gneg (term t)
  | Tapp (id, [t1; t2], _) when id == t_add_real -> 
      Gadd (term t1, term t2)
  | Tapp (id, [t1; t2], _) when id == t_sub_real -> 
      Gsub (term t1, term t2)
  | Tapp (id, [t1; t2], _) when id == t_mul_real -> 
      Gmul (term t1, term t2)
  | Tapp (id, [t1; t2], _) when id == t_div_real -> 
      Gdiv (term t1, term t2)
  (* float ops *)
  | Tapp (id, [t], _) when id == neg_float -> 
      Grnd (Gneg (term t))
  | Tapp (id, [t1; t2], _) when id == add_float -> 
      Grnd (Gadd (term t1, term t2))
  | Tapp (id, [t1; t2], _) when id == sub_float -> 
      Grnd (Gsub (term t1, term t2))
  | Tapp (id, [t1; t2], _) when id == mul_float -> 
      Grnd (Gmul (term t1, term t2))
  | Tapp (id, [t1; t2], _) when id == div_float -> 
      Grnd (Gdiv (term t1, term t2))
  | Tapp _ as t -> 
      assert false (*TODO: abstract*)

let add_ctx_vars =
  List.fold_left 
    (fun acc -> function Svar (id,_) -> Idset.add id acc | _ -> acc)

let rec intros ctx = function
  | Forall (true, id, n, t, p) ->
      (*let id' = next_away id (predicate_vars p) in*)
      let id' = next_away id (add_ctx_vars (predicate_vars p) ctx) in
      let p' = subst_in_predicate (subst_onev n id') p in
      intros (Svar (id', TTpure t) :: ctx) p'
  | Pimplies (true, a, b) -> 
      let h = fresh_hyp () in 
      intros (Spred (h, a) :: ctx) b
  | c -> 
      ctx, c


let rec split_ands = function
  | Pand (_, _, p1, p2) -> split_ands p1 @ split_ands p2
  | Pnamed (_, p) -> split_ands p
  | p -> [p]

(* recognition of a predicate as a Gappa predicate; raises Exit if it fails *)

type gappa_pred = 
  | Equation of (string * gterm)
  | Interval of (gterm * real_constant * real_constant)

let gpred = function
  | Papp (id, [Tvar x; t2], _) when is_eq id ->
      Equation (Ident.string x, term t2)
  | Pand (_, _, 
	  Papp (id1, [Tconst (ConstFloat f1); t1], _),
	  Papp (id2, [t2; Tconst (ConstFloat f2)], _))
    when id1 == t_le_real && id2 == t_le_real && t1 = t2 ->
      Interval (term t1, f1, f2)
  | _ ->
      raise Exit

(* split all the conjunctions  of an hypothesis, returning a list of equations
   and a list of Gin predicates *)
let rec hypothesis = function
  | Papp _ as p ->
      (try (match gpred p with Equation e -> [e],[] | Interval i -> [],[i])
       with Exit -> [],[])
  | Pand _ as p ->
      List.fold_left 
	(fun (eqs,ins) p -> let el,il = hypothesis p in el @ eqs, il @ ins)
	([],[]) (split_ands p)
  | Pnamed (_, p) -> 
      hypothesis p
  | Por _
  | Pif _
  | Piff _
  | Pnot _
  | Forall _
  | Forallb _
  | Exists _
  | Pfpi _
  | Ptrue | Pfalse | Pvar _ | Pimplies _ -> [], []

let context ctx = 
  assert false (*TODO*)

(* Processing obligations.
   One Why obligation can be split into several Gappa obligations *)

let queue = Queue.create ()

let reset () = Queue.clear queue

let process_obligation (_, _, (ctx, concl)) =
  let rec process ctx concl =
    let ctx,concl = intros ctx concl in
    match split_ands concl with
      | [] -> 
	  assert false
      | [p] -> 
	  begin match gpred concl with
	    | Interval (t,f1,f2) -> 
		let concl = Gin (t,f1,f2) in
		let eqs,ins = context ctx in
		let concl = match ins with
		  | [] -> concl
		  | p :: ins ->  
		      List.fold_right 
			(fun (t,f1,f2) p -> Gand (Gin (t,f1,f2), p)) ins concl
		in 
		Queue.add (eqs, concl) queue
	    | Equation _ -> 
		()
	  end
      | cl -> 
	  List.iter (process ctx) cl
  in
  process ctx concl

let push_obligations = List.iter process_obligation

let print_obligation fmt o =
  fprintf fmt "@rnd = %s\n" gappa_rnd;
  fprintf fmt "TODO"

let output_file fwe =
  let sep = "### DO NOT EDIT ABOVE THIS LINE" in
  let i = ref 0 in
  Queue.iter
    (fun o ->
       incr i;
       let file = fwe ^ "_why" ^ "_po_" ^ string_of_int !i ^ ".gappa" in
       do_not_edit_above ~file
	 ~before:(fun fmt -> print_obligation fmt o)
	 ~sep
	 ~after:(fun fmt -> ()))
    queue


