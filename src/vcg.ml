
(*s Verification Conditions Generator. *)

open Format
open Misc
open Util
open Options
open Logic
open Types
open Ast

(*s Sequents and obligations. *)

type context_element =
  | Svar of Ident.t * cc_type
  | Spred of Ident.t * predicate

type sequent = context_element list * predicate

type obligation = string * sequent

type proof = 
  | Lemma of string * Ident.t list
  | Reflexivity of term
  | Assumption of Ident.t

type validation = proof cc_term

(*s We automatically prove the trivial obligations *)

let reflexivity = function
  | Papp (id, [a;b]) when id == Ident.t_eq && a = b -> Reflexivity a
  | _ -> raise Exit

let assumption concl = function
  | Spred (id, p) when p = concl -> Assumption id 
  | _ -> raise Exit

let discharge ctx concl =
  try reflexivity concl with Exit -> list_first (assumption concl) ctx

let discharge_msg () =
  if !verbose then eprintf "one obligation trivially discharged...@\n"

(*s Cleaning the sequent: we remove variables not occuring at all in
    hypotheses or conclusion *)

let occur_in_hyp id = function
  | Spred (_,p) -> occur_predicate id p
  | Svar _ -> false

let clean_sequent hyps concl =
  let rec clean = function
    | [] ->
	[]
    | Svar (id, v) as h :: hl -> 
	if List.exists (occur_in_hyp id) hl || occur_predicate id concl then
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

(*s The VCG; it's trivial, we just traverse the CC term and push a 
    new obligation on each hole. *)

let vcg base t =
  let po = ref [] in
  let cpt = ref 0 in
  let push ctx concl = 
    incr cpt;
    let id = base ^ "_po_" ^ string_of_int !cpt in
    let ctx' = clean_sequent (List.rev ctx) concl in
    po := (id, (ctx', concl)) :: !po;
    Lemma (id, hyps_names ctx')
  in
  let rec traverse ctx = function
    | CC_var _ 
    | CC_expr _ 
    | CC_type _ as cc -> 
	cc
    | CC_hole p -> 
	CC_hole (try let pr = discharge ctx p in discharge_msg (); pr
		 with Exit -> push ctx p)
    | CC_letin (x, bl, e1, e2) -> 
	let e'1 = traverse ctx e1 in
	let e'2 = traverse (traverse_binders ctx bl) e2 in
	CC_letin (x, bl, e'1, e'2)
    | CC_lam (b, e) ->
	let e' = traverse (traverse_binders ctx [b]) e in
	CC_lam (b, e')
    | CC_app (e, el) ->
	let e' = traverse ctx e in
	let el' = List.map (traverse ctx) el in
	CC_app (e', el')
    | CC_tuple el ->
	let el' = List.map (traverse ctx) el in
	CC_tuple el'
    | CC_case (e, pl) ->
	let e' = traverse ctx e in
	let pl' = 
	  List.map (fun (bl,e) -> bl, traverse (traverse_binders ctx bl) e) pl
	in
	CC_case (e', pl')
    | CC_if (a, b, c) ->
	let a' = traverse ctx a in
	let b' = traverse ctx b in
	let c' = traverse ctx c in
	CC_if (a', b', c')
  and traverse_binder ctx = function
    | id, CC_var_binder v -> (Svar (id,v)) :: ctx
    | id, CC_pred_binder p -> (Spred (id,p)) :: ctx
    | id, CC_untyped_binder -> assert false
  and traverse_binders ctx = 
    List.fold_left traverse_binder ctx
  in
  let cc' = traverse [] t in
  List.rev !po, cc'

