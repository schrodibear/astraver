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

type obligation = Loc.t * string * sequent

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
  | ProofTerm of proof cc_term

type validation = proof cc_term

(*s Log for the why-viewer *)

let logs = ref ([] : Log.t)

let log_print_function = 
  ref (fun fmt (_,p) -> fprintf fmt "@[%a@]@?" print_predicate p)

let log l sq lemma_name =
  if wol then
    let s = 
      let buf = Buffer.create 1024 in
      let fmt = formatter_of_buffer buf in
      !log_print_function fmt sq;
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

(* ..., h:false=true, ... |- C *)
let discriminate_lemma = Ident.create "why_boolean_discriminate"
let discriminate ctx concl = 
  let false_eq_true = 
    equality (Tconst (ConstBool false)) (Tconst (ConstBool true))
  in
  let h = lookup_hyp false_eq_true ctx in
  ProofTerm 
    (cc_applist (CC_var discriminate_lemma) [CC_var h; CC_type (TTpred concl)])

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

(* unification of terms *)
let rec unif_term u = function
  | Tconst c, Tconst c' when c = c' -> u
  | Tvar id, Tvar id' when id == id' -> u
  | Tderef _, _ | _, Tderef _ -> assert false
  | Tvar id, t' -> 
      (try (match Idmap.find id u with
	      | None -> Idmap.add id (Some t') u
	      | Some t'' -> if t' = t'' then u else raise Exit)
       with Not_found -> raise Exit)
  | Tapp (id, tl), Tapp (id', tl') when id == id' -> unif_terms u (tl, tl')
  | _ -> raise Exit
and unif_terms u = function
  | [], [] -> u
  | t :: tl, t' :: tl' -> unif_terms (unif_term u (t, t')) (tl, tl')
  | _ -> raise Exit

(* unification of predicates *)
let rec unif_pred u = function
  | Pvar id, Pvar id' when id == id' -> u
  | Papp (id, tl), Papp (id', tl') when id == id' -> unif_terms u (tl, tl')
  | Ptrue, Ptrue | Pfalse, Pfalse -> u
  | Forallb (_, _, _, a, b), Forallb (_, _, _, a', b')
  | Pimplies (a, b), Pimplies (a', b') 
  | Pand (a, b), Pand (a', b')
  | Por (a, b), Por (a', b') -> unif_pred (unif_pred u (a, a')) (b, b')
  | Pif (a, b, c), Pif (a', b', c') ->
      unif_pred (unif_pred (unif_term u (a, a')) (b, b')) (c, c')
  | Pif (Tvar x, b, c), p' ->
      (try match Idmap.find x u with
	 | None -> 
	     (try unif_pred (Idmap.add x (Some ttrue) u) (b, p')
	      with Exit -> unif_pred (Idmap.add x (Some tfalse) u) (c, p'))
	 | Some (Tconst (ConstBool true)) -> unif_pred u (b, p')
	 | Some (Tconst (ConstBool false)) -> unif_pred u (c, p')
	 | _ -> raise Exit
       with Not_found ->
	 raise Exit)
  | Pnot a, Pnot a' -> unif_pred u (a, a')
  | Forall (_, n, _, p), Forall (_, n', _, p') 
  | Exists (_, n, _, p), Exists (_, n', _, p') ->
      let p'n = subst_in_predicate (subst_onev n' n) p' in 
      unif_pred u (p, p'n)
  | _ -> raise Exit

(* [lookup_instance]. 
   [id] is a proof of [forall v1...vn . p => q] where [bvars = v1...vn].
   we look for an hypothesis matching [p], as an instance [p(a1...ak)],
   and we return [forall vi. q(a1...ak)] (together with a proof of it)
   where the [vi]s not in the [aj]s. *)

let first_hyp f = 
  list_first (function Svar _ -> raise Exit | Spred (h, p) -> f h p)

let lookup_instance id bvars p q hpx p' =
  let u0 = 
    List.fold_right (fun (_,n,_) -> Idmap.add n None) bvars Idmap.empty 
  in
  let u = unif_pred u0 (p, p') in
  let bvars',vars,s =
    List.fold_right 
      (fun ((x,n,_) as b) (bv,vl,s) -> match Idmap.find n u with
	 | None -> b :: bv, (Tvar x) :: vl, s
	 | Some x' -> bv, x' :: vl, Idmap.add n x' s) 
      bvars ([], [], Idmap.empty)
  in
  List.fold_right
    (fun (x, n, ty) p -> Forall (x, n, ty, p))
    bvars' (simplify (tsubst_in_predicate s q)),
  cc_lam 
    (List.map (fun (x, _, ty) -> x, CC_var_binder (TTpure ty)) bvars')
    (cc_applist id (List.map cc_term (vars @ [Tvar hpx])))

(* checks whether [p] is an instance of [c] and returns the instance *)
let unify bvars p c =
  let u0 = 
    List.fold_right (fun (_,n,_) -> Idmap.add n None) bvars Idmap.empty 
  in
  let u = unif_pred u0 (p, c) in
  List.map
    (fun (_,n,_) -> match Idmap.find n u with
       | None -> raise Exit (* does not instanciate all variables *)
       | Some x -> x) bvars

(* alpha-equivalence over predicates *)
let alpha a b = 
  try let _ = unif_pred Idmap.empty (a, b) in true with Exit -> false

let lookup_boolean_instance a b =
  let rec lookup = function
    | Svar (x, TTpure PTbool) ::
      Spred (h, Pif (Tvar x1, c, d)) :: _ when x == x1 && a = c && b = d -> 
	x, h
    | _ :: ctx ->
	lookup ctx
    | [] ->
	raise Exit
  in
  lookup

let boolean_wp_lemma = Ident.create "why_boolean_wp"

(* [qe_forall (forall x1...forall xn. p) = [x1;...;xn],p] *)
let rec qe_forall = function
  | Forall (id, n, ty, p) -> 
      let vl, p = qe_forall p in (id, n, ty) :: vl, p
  | Forallb (id, n, p, _, _) -> 
      let vl, p = qe_forall p in (id, n, PTbool) :: vl, p
  | p -> 
      [], p

(* introduction of universal quantifiers and implications;
   return the new goal (context-conclusion), together with a proof-term
   modifier to apply to the proof-term found for the new goal. *)
let rec intros ctx = function
  | Forall (id, n, t, p) ->
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      let ctx', concl', f = intros (Svar (id', TTpure t) :: ctx) p' in
      ctx', concl',
      (fun pr -> 
	 ProofTerm (cc_lam [id', CC_var_binder (TTpure t)] (CC_hole (f pr))))
  | Pimplies (a, b) -> 
      let h = fresh_hyp () in 
      let ctx', concl', f = intros (Spred (h, a) :: ctx) b in
      ctx', concl', 
      (fun pr -> ProofTerm (cc_lam [h, CC_pred_binder a] (CC_hole (f pr))))
  | c -> 
      ctx, c, (fun pr -> pr)

let boolean_forall_lemma = Ident.create "why_boolean_forall"
let make_forall_proof id = function
  | Forall _ -> 
      CC_var id
  | Forallb (_, n, q, _, _) -> 
      cc_applist (CC_var boolean_forall_lemma) 
	[cc_lam [n, CC_var_binder (TTpure PTbool)] (CC_type (TTpred q)); 
	 CC_var id]
  | _ -> 
      assert false

(* Tautologies in linear minimal first-order logic.
   Context [ctx] is given in reverse order ([ctx = xk:tk, ..., x1:t1]). 

   First, we introduce universal quantifiers and implications with [intros].

   Then, we cut the context at the last [WP] and reverse it at the same
   time, with [cut_context].

   Then we apply the linear rules: assumption, and-elimination,
   forall-elimination and implication-elimination. Regarding 
   forall-elimination, there are two cases: (1) the hypothesis is
   [forall x. P] and the goal matches [P], and (2) the hypothesis
   is [forall x. P => Q] and there is another hypothesis matching [P]. *)

let linear ctx concl = 
  let ctx, concl, pr_intros = intros ctx concl in
  (* we cut the context at the last WP (and reverse it) *)
  let rec cut_context acc = function
    | [] -> raise Exit
    | Spred (id, _) as h :: _ when is_wp id -> h :: acc
    | h :: ctx -> cut_context (h :: acc) ctx
  in
  let ctx = cut_context [] ctx in
  let rec search = function
    | [] -> 
	raise Exit
    (* assumption *)
    | Spred (id, p) :: _ when p = concl -> (* alpha-equivalence ? *)
	Assumption id
    (* and-elimination *)
    | Spred (id, Pand (a, b)) :: ctx ->
	begin try
	  search ctx
	with Exit ->
	  let h1 = fresh_hyp () in
	  let h2 = fresh_hyp () in
	  let ctx' = (Spred (h1, a)) :: (Spred (h2, b)) :: ctx in
	  ProofTerm (CC_letin (false,
			       [h1, CC_pred_binder a; h2, CC_pred_binder b],
			       CC_var id, CC_hole (search ctx')))
	end
    (* forall-elimination *)
    | Spred (id, (Forall _ | Forallb _ as a)) :: ctx -> 
	let id = make_forall_proof id a in
	begin try
	  search ctx
	with Exit ->
	  let bvars,p = qe_forall a in
	  try
	    (* 1. try to unify [p] and [concl] *)
	    let vars = unify bvars p concl in
	    ProofTerm (cc_applist id (List.map cc_term vars))
	  with Exit -> match p with
	    | Pimplies (p, q) ->
  	    (* 2. we have [p => q]: try to unify [p] and an hypothesis *)
		first_hyp 
		  (fun h ph ->
		     let qx,pr_qx = lookup_instance id bvars p q h ph in
		     let h1 = fresh_hyp () in
		     let ctx' = Spred (h1, qx) :: ctx in
		     ProofTerm 
		       (CC_letin (false, [h1, CC_pred_binder qx], pr_qx,
				  CC_hole (search ctx'))))
		  ctx
	    | Pand (p1, p2) ->
            (* 3. we have [a and b]: split under the quantifiers *)
                let h1 = fresh_hyp () in
		let h2 = fresh_hyp () in
		let qpi pi =
		  List.fold_right
		    (fun (x, n, ty) p -> Forall (x, n, ty, p)) bvars pi
		in
		let qp1 = qpi p1 in
		let qp2 = qpi p2 in
		let ctx' = Spred (h1, qp1) :: Spred (h2, qp2) :: ctx in
		let pr = search ctx' in
		let pr_qpi hi = 
		  cc_lam 
		    (List.map (fun (x,_,ty) -> x, CC_var_binder (TTpure ty)) 
		       bvars)
		    (CC_letin (false, [h1, CC_pred_binder p1;
				       h2, CC_pred_binder p2], 
			       cc_applist id
				 (List.map (fun (_,x,_) -> CC_var x) bvars),
			       CC_var hi))
		in
		ProofTerm 
		  (CC_letin (false, [h1, CC_pred_binder qp1], pr_qpi h1,
   	           CC_letin (false, [h2, CC_pred_binder qp2], pr_qpi h2,
			     CC_hole pr)))
	    | _ ->
		raise Exit
	end
    (* implication-elimination *)
    | Spred (id, Pimplies (p, q)) :: ctx -> (* alpha-equivalence ? *)
	begin try

	  search ctx
	with Exit ->
	  let hp = lookup_hyp p ctx in
	  let hq = fresh_hyp () in
	  let ctx' = Spred (hq, q) :: ctx in
	  ProofTerm
	    (CC_letin (false, [hq, CC_pred_binder q],
		       CC_app (CC_var id, CC_var hp), CC_hole (search ctx')))
	end
    (* skip this hypothesis (or variable) *)
    | _ :: ctx ->
	search ctx
  in
  pr_intros (search ctx)

(* ..., v=t, p(v) |- p(t) *)
let rewrite_var_lemma = Ident.create "why_rewrite_var"
let rewrite_var ctx concl = match ctx, concl with
  | Spred (h1, p1) ::
    Svar (id'1, TTpure PTbool) ::
    Spred (h2, Papp (ide, [Tvar v; t])) ::
    Svar (v', ty) :: _,
    p
    when is_eq ide && v == v' -> 
      if tsubst_in_predicate (subst_one v t) p1 <> p then raise Exit;
      ProofTerm 
	(cc_applist (CC_var rewrite_var_lemma)
	   [CC_var h2;
	    CC_type (TTlambda ((v, CC_var_binder ty), TTpred p1));
	    CC_var h1])
  | _ -> 
      raise Exit

(* ..., x:bool, if x then a else b |- if x then c else d *)
let boolean_case_lemma = Ident.create "why_boolean_case"
let boolean_case ctx concl = match ctx, concl with
  | Spred (h1, Pif (Tvar x1, a, b)) ::
    Svar (x, TTpure PTbool) ::
    ctx,
    Pif (Tvar x2, c, d)
    when x1 == x && x2 == x ->
      let h2 = fresh_hyp () in
      let branch h p =
	let pr = linear (Spred (h2, h) :: ctx) p in
	CC_lam ((h2, CC_pred_binder h), CC_hole pr)
      in
      ProofTerm
	(cc_applist (CC_var boolean_case_lemma)
	   [CC_var h1; branch a c; branch b d])
  | _ ->
      raise Exit

(* we try the automatic proofs successively, starting with the simplest ones *)
let discharge_methods ctx concl =
  try ptrue concl with Exit ->
  try wf_zwf concl with Exit ->
  try reflexivity concl with Exit -> 
  try absurd ctx with Exit ->
  try list_first (assumption concl) ctx with Exit ->
  try conjunction ctx concl with Exit ->
  try loop_variant_1 ctx concl with Exit ->
  try rewrite_var ctx concl with Exit ->
  try discriminate ctx concl with Exit ->
  try linear ctx concl with Exit ->
  boolean_case ctx concl

(* DEBUG *)
let print_sequent fmt (ctx, concl) =
  let print_hyp fmt = function
    | Svar (id, _) -> Ident.print fmt id
    | Spred (id, p) -> fprintf fmt "%a: %a" Ident.print id print_predicate p
  in
  fprintf fmt "@[[@\n%a@\n----@\n%a@\n]@]" (print_list newline print_hyp) ctx
    print_predicate concl
  
let count = ref 0

let discharge loc ctx concl =
  let pr = discharge_methods ctx concl in
  log (snd loc) (ctx, concl) None;
  incr count;
  if_verbose_2 eprintf "one obligation trivially discharged [%d]@." !count;
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
    | Svar (y, _) :: _ as hl when x = y -> hl
    | Spred (_, p) :: hl when occur_predicate x p -> filter_up_to x hl
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
    | Spred (_, Ptrue) :: hl ->
	clean hl
    | Spred (id, _) :: hl when is_wp id ->
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

let rec annotated_if id = function
  | [id', CC_var_binder (TTpure PTbool); _, CC_pred_binder _] -> id == id'
  | [] -> false
  | _ :: bl -> annotated_if id bl

let rec annotation_if = function
  | [qb, CC_pred_binder q] -> qb, q
  | _ :: bl -> annotation_if bl
  | [] -> assert false

(***
let simplify_sequent ctx p = 
  let simplify_hyp = function
    | Svar _ as h -> h
    | Spred (id, p) -> Spred (id, simplify p)
  in
  List.map simplify_hyp ctx, simplify p
***)

(*s The VCG; it's trivial, we just traverse the CC term and push a 
    new obligation on each hole. *)

let vcg base t =
  let po = ref [] in
  let cpt = ref 0 in
  let push loc ctx concl = 
    incr cpt;
    let id = base ^ "_po_" ^ string_of_int !cpt in
    let ctx' = clean_sequent (List.rev ctx) concl in
    let sq = (ctx', concl) in
    po := (loc, id, sq) :: !po;
    log (snd loc) sq (Some id);
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
    | CC_letin (dep, bl1, e1, 
		CC_if (CC_term (Tvar idb),
		       (CC_lam ((_, CC_pred_binder _), _) as br1),
		       (CC_lam ((_, CC_pred_binder _), _) as br2)))
      when annotated_if idb bl1 ->
	let e'1 = traverse ctx e1 in
	let ctx = traverse_binders ctx (cut_last_binders bl1) in
	let br'1 = traverse ctx br1 in
	let br'2 = traverse ctx br2 in
	CC_letin (dep, bl1, e'1, CC_if (CC_var idb, br'1, br'2))
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

