
(*s Verification Conditions Generator. *)

open Format
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
  | Reflexivity of term
  | Assumption of Ident.t
  | Proj1 of Ident.t
  | Conjunction of Ident.t * Ident.t

type validation = proof cc_term

(*s We automatically prove the trivial obligations *)

let is_eq id = id == Ident.t_eq || id == Ident.t_eq_int

let reflexivity = function
  | Papp (id, [a;b]) when is_eq id && a = b -> Reflexivity a
  | _ -> raise Exit

let assumption concl = function
  | Spred (id, p) when p = concl -> Assumption id 
  | Spred (id, Pand (a, b)) when a = concl -> Proj1 id
  | _ -> raise Exit

let lookup_hyp a = 
  let test = function Spred (id, b) when a = b -> id | _ -> raise Exit in
  list_first test

let conjunction ctx = function
  | Pand (a, b) -> Conjunction (lookup_hyp a ctx, lookup_hyp b ctx)
  | _ -> raise Exit

let discharge ctx concl =
  try reflexivity concl with Exit -> 
  try list_first (assumption concl) ctx with Exit ->
  conjunction ctx concl

let discharge_msg () =
  if_verbose eprintf "one obligation trivially discharged@."

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
    | CC_term _ 
    | CC_type _ as cc -> 
	cc
    | CC_hole p -> 
	CC_hole (try let pr = discharge ctx p in discharge_msg (); pr
		 with Exit -> push ctx p)
    (* special treatment for the if-then-else *)
    | CC_letin (x, ([idb, CC_var_binder (TTpure PTbool); 
		     _, CC_pred_binder _] as bl1), e1, 
		CC_if (CC_term (Tvar idb'),
		       (CC_lam ((_, CC_pred_binder _), _) as br1),
		       (CC_lam ((_, CC_pred_binder _), _) as br2)))
      when idb = idb' ->
	let e'1 = traverse ctx e1 in
	let br'1 = traverse ctx br1 in
	let br'2 = traverse ctx br2 in
	CC_letin (x, bl1, e'1, CC_if (CC_var idb', br'1, br'2))
    | CC_letin (x, bl, e1, e2) -> 
	let e'1 = traverse ctx e1 in
	let e'2 = traverse (traverse_binders ctx bl) e2 in
	CC_letin (x, bl, e'1, e'2)
    | CC_lam (b, e) ->
	let e' = traverse (traverse_binders ctx [b]) e in
	CC_lam (b, e')
    | CC_app (f, a) ->
	let f' = traverse ctx f in
	let a' = traverse ctx a in
	CC_app (f', a')
    | CC_tuple (el,p) ->
	let el' = List.map (traverse ctx) el in
	CC_tuple (el',p)
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

