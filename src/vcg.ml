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

(*s Verification Conditions Generator. *)

open Format
open Ident
open Misc
open Util
open Options
open Logic
open Types
open Cc

(*s Sequents and obligations. *)

type context_element =
  | Svar of Ident.t * cc_type
  | Spred of Ident.t * predicate

type sequent = context_element list * predicate

type obligation = string * sequent

type proof = 
  | Lemma of string * Ident.t list
  | True
  | Reflexivity of term
  | Assumption of Ident.t
  | Proj1 of Ident.t
  | Conjunction of Ident.t * Ident.t
  | WfZwf of term
  | Loop_variant_1 of Ident.t * Ident.t
  | Absurd of Ident.t

type validation = proof cc_term

(*s Log for the why-viewer *)

let logs = ref ([] : Log.t)

let log l p lemma_name =
  if wol then
    let s = 
      let buf = Buffer.create 1024 in
      let fmt = formatter_of_buffer buf in
      fprintf fmt "@[%a@]@?" print_predicate p;
      Buffer.contents buf
    in
    if_debug (fun () -> eprintf "at %d, %b, %s@\n" l (lemma_name = None) s) ();
    logs := (l, s, lemma_name) :: !logs

(*s We automatically prove the trivial obligations *)

(* ... |- true *)
let ptrue = function
  | Ptrue -> True
  | _ -> raise Exit

let is_eq id = id == Ident.t_eq || id == Ident.t_eq_int

(* ... |- a=a *)
let reflexivity = function
  | Papp (id, [a;b]) when is_eq id && a = b -> Reflexivity a
  | _ -> raise Exit

(* ..., h:P, ...|- P  and ..., h:P and Q, ...|- P *)
let assumption concl = function
  | Spred (id, p) when p = concl -> Assumption id 
  | Spred (id, Pand (a, b)) when a = concl -> Proj1 id
  | _ -> raise Exit

let lookup_hyp a = 
  let test = function Spred (id, b) when a = b -> id | _ -> raise Exit in
  list_first test

(* ..., h:False, ... |- C *)
let absurd ctx =  Absurd (lookup_hyp Pfalse ctx)

(* ..., h:A, ..., h':B, ... |- A and B *)
let conjunction ctx = function
  | Pand (a, b) -> Conjunction (lookup_hyp a ctx, lookup_hyp b ctx)
  | _ -> raise Exit

(* ... |- (well_founded (Zwf 0)) *)
let wf_zwf = function
  | Papp (id, [Tvar id']) when id == well_founded && id' == t_zwf_zero ->
      WfZwf (Tconst (ConstInt 0))
  | _ -> 
      raise Exit

(* ..., h:v=phi0, ..., h':I and (Zwf c phi1 phi0), ... |- (Zwf c phi1 v) *)
let loop_variant_1 hyps concl =
  let lookup_h v = function
    | Spred (h, Papp (id, [Tvar id';phi0])) when is_eq id && id' == v -> h,phi0
    | _ -> raise Exit
  in
  let rec lookup_h' phi1 phi0 = function
    | Spred (h', Pand (_, Papp (id, [t1; t0]))) 
      when id == t_zwf_zero && t1 = phi1 && t0 = phi0 -> h'
    | _ -> raise Exit
  in
  match concl with
    | Papp (id, [phi1; Tvar v]) when id == t_zwf_zero ->
	let h, phi0 = list_first (lookup_h v) hyps in 
	let h' = list_first (lookup_h' phi1 phi0) hyps in
	Loop_variant_1 (h, h')
    | _ -> 
	raise Exit

let discharge_methods ctx concl =
  try ptrue concl with Exit ->
  try wf_zwf concl with Exit ->
  try reflexivity concl with Exit -> 
  try absurd ctx with Exit ->
  try list_first (assumption concl) ctx with Exit ->
  try conjunction ctx concl with Exit ->
  loop_variant_1 ctx concl

let discharge loc ctx concl =
  let pr = discharge_methods ctx concl in
  log (snd loc) concl None;
  if_verbose eprintf "one obligation trivially discharged@.";
  pr

(*s Cleaning the sequents *)

let occur_in_hyp id = function
  | Spred (_,p) -> occur_predicate id p
  | Svar _ -> false

let occur_as_var id = function
  | Svar (id',_) -> id = id'
  | Spred _ -> false

let clean_sequent hyps concl =
  (* if a variable appears twice, we remove the first and its dependencies *)
  let rec filter_up_to x = function
    | [] -> []
    | Svar (y,_) :: _ as hl when x = y -> hl
    | Spred (_,p) :: hl when occur_predicate x p -> filter_up_to x hl
    | h :: hl -> h :: filter_up_to x hl
  in
  (* we remove variables not occuring at all in hypotheses or conclusion *)
  let rec clean = function
    | [] ->
	[]
    | Svar (x, v) as h :: hl -> 
	if List.exists (occur_as_var x) hl then
	  clean (filter_up_to x hl)
	else if List.exists (occur_in_hyp x) hl || occur_predicate x concl then
	  h :: clean hl
	else
	  clean hl
    | h :: hl ->
	h :: clean hl
  in
  clean hyps

let hyps_names = 
  let hyp_name = function Svar (id,_) | Spred (id,_) -> id in
  List.map hyp_name

let rec cut_last_binders = function
  | [] | [_] | [_; _] -> []
  | b :: bl -> b :: cut_last_binders bl

(*s The VCG; it's trivial, we just traverse the CC term and push a 
    new obligation on each hole. *)

let vcg base t =
  let po = ref [] in
  let cpt = ref 0 in
  let push loc ctx concl = 
    incr cpt;
    let id = base ^ "_po_" ^ string_of_int !cpt in
    log (snd loc) concl (Some id);
    let ctx' = clean_sequent (List.rev ctx) concl in
    po := (id, (ctx', concl)) :: !po;
    Lemma (id, hyps_names ctx')
  in
  let rec traverse ctx = function
    | CC_var _ 
    | CC_term _ 
    | CC_type _ as cc -> 
	cc
    | CC_hole (loc, p) -> 
	CC_hole (try discharge loc ctx p with Exit -> push loc ctx p)
    (* special treatment for the if-then-else *)
    | CC_letin (dep, ([idb, CC_var_binder (TTpure PTbool); 
		       _, CC_pred_binder _] as bl1), e1, 
		CC_if (CC_term (Tvar idb'),
		       (CC_lam ((_, CC_pred_binder _), _) as br1),
		       (CC_lam ((_, CC_pred_binder _), _) as br2)))
      when idb = idb' ->
	let e'1 = traverse ctx e1 in
	let br'1 = traverse ctx br1 in
	let br'2 = traverse ctx br2 in
	CC_letin (dep, bl1, e'1, CC_if (CC_var idb', br'1, br'2))
    (* special treatment for the composition of exceptions *)
    | CC_letin (dep, bl, e1, CC_case (CC_term (Tvar _) as e2, br)) ->
	let e'1 = traverse ctx e1 in
	let ctx = traverse_binders ctx bl in
	let br' = List.map (traverse_case ctx) br in
	CC_letin (dep, bl, e'1, CC_case (e2, br'))
    | CC_letin (dep, bl, e1, CC_case (e2, br)) ->
	let e'1 = traverse ctx e1 in
	let ctx = traverse_binders ctx (cut_last_binders bl) in
	let e'2 = traverse ctx e2 in
	let br' = List.map (traverse_case ctx) br in
	CC_letin (dep, bl, e'1, CC_case (e'2, br'))
    | CC_letin (dep, bl, e1, e2) -> 
	let e'1 = traverse ctx e1 in
	let e'2 = traverse (traverse_binders ctx bl) e2 in
	CC_letin (dep, bl, e'1, e'2)
    | CC_lam (b, e) ->
	let e' = traverse (traverse_binders ctx [b]) e in
	CC_lam (b, e')
    | CC_app (f, a) ->
	let f' = traverse ctx f in
	let a' = traverse ctx a in
	CC_app (f', a')
    | CC_case (e, pl) ->
	let e' = traverse ctx e in
	let pl' = List.map (traverse_case ctx) pl in
	CC_case (e', pl')
    | CC_tuple (el,p) ->
	let el' = List.map (traverse ctx) el in
	CC_tuple (el',p)
    | CC_if (a, b, c) ->
	let a' = traverse ctx a in
	let b' = traverse ctx b in
	let c' = traverse ctx c in
	CC_if (a', b', c')
  and traverse_case ctx (p,e) =
    p, traverse (traverse_pattern ctx p) e
  and traverse_pattern ctx = function
    | PPvariable (id,b) -> traverse_binder ctx (id,b)
    | PPcons (_, pl) -> List.fold_left traverse_pattern ctx pl
  and traverse_binder ctx = function
    | id, CC_var_binder v -> (Svar (id,v)) :: ctx
    | id, CC_pred_binder p -> (Spred (id,p)) :: ctx
    | id, CC_untyped_binder -> assert false
  and traverse_binders ctx = 
    List.fold_left traverse_binder ctx
  in
  let cc' = traverse [] t in
  List.rev !po, cc'

