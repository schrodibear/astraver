(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: wp.ml,v 1.18 2002-03-11 15:17:58 filliatr Exp $ i*)

open Format
open Ident
open Logic
open Misc
open Types
open Ast
open Util
open Env
open Effect
open Typing
open Rename

(* force a post-condition *)

let force_post env q e = match q with
  | None -> 
      e
  | Some { a_value = c } ->
      let ids = predicate_refs env c in
      let ef = Effect.add_reads ids e.info.kappa.c_effect in
      let k = { e.info.kappa with c_post = q; c_effect = ef } in
      let i = { e.info with kappa = k } in
      { desc = e.desc; info = i }

let post_if_none env q p = match post p with
  | None -> force_post env q p 
  | _ -> p

let optpost_app f = option_app (post_app f)

(* misc. *)

let create_bool_post c =
  Some { a_value = c; a_name = Name (bool_name()) }

let is_conditional p = match p.desc with If _ -> true | _ -> false

(* [extract_pre p] erase the pre-condition of [p] and returns it *)

let extract_pre pr =
  { desc = pr.desc; 
    info = { pr.info with kappa = { pr.info.kappa with c_pre = [] } } },
  pr.info.kappa.c_pre

(* adds some pre-conditions *)

let add_pre p1 pr =
  let k = pr.info.kappa in
  let p' = p1 @ k.c_pre in
  { desc = pr.desc; 
    info = {  pr.info with kappa = { k with c_pre = p' } } }
  
(* change the statement *)

let change_desc p d = { p with desc = d }

(* [normalize_boolean b] checks if the boolean expression [b] (of type
   [bool]) is annotated; if not, tries to add the annotation 
   [if result then c=true else c=false]) if [b] is an expression [c]. *)

let is_bool = function
  | PureType PTbool -> true
  | _ -> false

(* top point of a program *)

let top_point = function
  | PPoint (s,_) as p -> s,p
  | p -> let s = label_name () in s, PPoint(s,p)

let top_point_block = function
  | (Label s :: _) as b -> s,b
  | b -> let s = label_name () in s, (Label s)::b

(*s Normalization. In this first pass, we
    (2) annotate [x := E] with [{ x = E }]
    (3) give tests the right postconditions
    (4) lift preconditions up in assignements *)

let lift_pre p = match p.desc with
  | Aff (x,e) ->
      let e1,p1 = extract_pre e in
      change_desc (add_pre p1 p) (Aff (x,e1))
  | TabAff (check, x, ({ desc = Expression _ } as e1), e2) ->
      let e1',p1 = extract_pre e1 in
      let e2',p2 = extract_pre e2 in
      change_desc (add_pre (p1 @ p2) p) (TabAff (check,x,e1',e2'))
  | _ ->
      p

let rec normalize p =
  let env = p.info.env in
  let p = lift_pre p in
  let k = p.info.kappa in
  match p.desc with
    | Aff (x, { desc = Expression t }) when k.c_post = None ->
	let t = make_after_before_term env t in
	let q = create_bool_post (equality (Tvar x) t) in
	post_if_none env q p
    | Aff (x, e) ->
	change_desc p (Aff (x, normalize e))
    | If (e1, e2, e3) ->
	change_desc p (If (normalize_boolean env e1, 
			   normalize e2, normalize e3))
    | Acc _ | Var _ | Expression _ ->
	p
    | TabAcc (b, x, e) ->
	change_desc p (TabAcc (b, x, normalize e))
    | TabAff (b, x, e1, e2) ->
	change_desc p (TabAff (b, x, normalize e1, normalize e2))
    | Seq bl ->
	change_desc p (Seq (normalize_block bl))
    | Lam (bl, e) ->
	change_desc p (Lam (bl, normalize e))
    | While (b, invopt, var, bl) ->
	change_desc p (While (normalize_boolean env b,
			      invopt, var, normalize_block bl))
    | LetRef (x, ({ desc = Expression t } as e1), e2) 
      when e1.info.kappa.c_post = None ->
	let t = make_after_before_term env t in
	let q = create_bool_post (equality (Tvar Ident.result) t) in
	change_desc p (LetRef (x, post_if_none env q e1, normalize e2))
    | LetRef (x, e1, e2) ->
	change_desc p (LetRef (x, normalize e1, normalize e2))
    | LetIn (x, e1, e2) ->
	change_desc p (LetIn (x, normalize e1, normalize e2))
    | LetRec (x, bl, v, var, e1) ->
	change_desc p (LetRec (x, bl, v, var, normalize e1))
    | App (e1, Term e2) ->
	change_desc p (App (normalize e1, Term (normalize e2)))
    | App (e1, (Refarg _ as r)) ->
	change_desc p (App (normalize e1, r))
    | App (e1, Type v) ->
	change_desc p (App (normalize e1, Type v))
    | Coerce e ->
	let e = normalize e in
	if k.c_post = None then
	  let ke = e.info.kappa in
	  let k' = { ke with c_pre = k.c_pre @ ke.c_pre } in
	  { desc = e.desc; info = { e.info with kappa = k'} }
	else
	  change_desc p (Coerce e)
    | PPoint (lab, d) ->
	let p = normalize (change_desc p d) in
	change_desc p (PPoint (lab, p.desc))

and normalize_block = function
  | [] ->
      []
  | Statement p :: bl ->
      let p' = normalize p in
      let bl' = normalize_block bl in
      Statement p' :: bl'
  | Label l :: bl ->
      let bl' = normalize_block bl in
      Label l :: bl'
  | Assert p :: bl ->
      let bl' = normalize_block bl in
      Assert p :: bl'

and normalize_boolean env b =
  let k = b.info.kappa in
  let give_post b q =
    { b with info = { b.info with kappa = { k with c_post = q } } }
  in
  let q = k.c_post in
  match q with
    | Some _ ->
	(* a postcondition; nothing to do *)
	normalize (give_post b (force_bool_name q))
    | None -> begin
	match b.desc with
	  | Expression c ->
	      (* expression E -> if result then E=true else E=false *)
	      let c = Pif (Tvar Ident.result, 
			   equality c ttrue, equality c tfalse) in
	      give_post b (create_bool_post c)
	  | If (e1, e2, e3) ->
	      let ne1 = normalize_boolean env e1 in
	      let ne2 = normalize_boolean env e2 in
	      let ne3 = normalize_boolean env e3 in
	      let q1t,q1f = decomp_boolean (post ne1) in
	      let q2t,q2f = decomp_boolean (post ne2) in
	      let q3t,q3f = decomp_boolean (post ne3) in
	      let c = Pif (Tvar Ident.result,
			   por (pand q1t q2t) (pand q1f q3t),
			   por (pand q1t q2f) (pand q1f q3f)) in
	      let b' = change_desc b (If (ne1,ne2,ne3)) in
	      give_post b' (create_bool_post c)
	  | _ -> 
	      normalize b
      end

(*s WP. [wp p q] computes the weakest precondition [wp(p,q)]
    and gives postcondition [q] to [p] if necessary. *)

let output p = 
  let w = Effect.get_writes (effect p) in
  let env = p.info.env in
  List.map (fun id -> (id, type_in_env env id)) w

let rec wp p q =
  let env = p.info.env in
  let postp = post p in
  let q0 = if postp = None then q else postp in
  let lab = p.info.label in
  let q1 = optpost_app (change_label "" lab) q0 in
  let d,w = wp_desc p.info p.desc q1 in
  let w = optpost_app (erase_label lab) w in
  let p = if postp = None then force_post env q0 p else p in
  let w = match postp, q with
    | Some {a_value=q'}, Some {a_value=q} ->
	let vars = (result, result_type p) :: (output p) in
	Some (anonymous (foralls vars (Pimplies (q', q))))
    | _ -> 
	w
  in
  p, w

and wp_desc info d q = 
  let result = info.kappa.c_result_name in
  match d with
    (* TODO: check if likely *)
    | Var x ->
	d, optpost_app (tsubst_in_predicate [result,Tvar x]) q
    (* $wp(E,q) = q[result \leftarrow E]$ *)
    | Expression t ->
	d, optpost_app (tsubst_in_predicate [result,t]) q
    (* $wp(!x,q) = q[result \leftarrow x]$ *)
    | Acc x ->
	d, optpost_app (subst_in_predicate [result,x]) q
    (* $wp(x := e, q) = wp(e, q[result\leftarrow void; x\leftarrow result])$ *)
    | Aff (x, p) ->
	let q = optpost_app (tsubst_in_predicate [result, tvoid]) q in
	let q = optpost_app (subst_in_predicate [x, result]) q in
	let p',w = wp p q in
	Aff (x, p'), w
    | TabAcc _ ->
	failwith "todo: wp tab acc"
    | TabAff _ ->
	failwith "todo: wp tab aff"
    (* conditional: two cases depending on [p1.post] *)
    | If (p1, p2, p3) ->
	let p'2,w2 = wp p2 q in
	let p'3,w3 = wp p3 q in
	(match w2, w3, post p1 with
	   (***
	   | Some {a_value=q2}, Some {a_value=q3}, Some {a_value=q1} -> 
	       (* $wp(if p1 then p2 else p3, q) = 
		  q1(true) => wp(p2, q) and q1(false) => wp(p3, q)$ *)
	       let q1 = make_before_after q1 in
	       let q1t = tsubst_in_predicate [Ident.result,ttrue] q1 in
	       let q1f = tsubst_in_predicate [Ident.result,tfalse] q1 in
	       let w = Pand (Pimplies (q1t, q2), Pimplies (q1f, q3)) in
	       If (p1, p'2, p'3), create_bool_post w
           ***)
	   | Some {a_value=q2}, Some {a_value=q3}, _ -> 
	       (* $wp(if p1 then p2 else p3, q) = 
		  wp(p1, if result then wp(p2, q) else wp(p3, q))$ *)
	       let result1 = p1.info.kappa.c_result_name in
	       let q1 = Pif (Tvar result1, q2, q3) in
	       let p'1,w1 = wp p1 (create_bool_post q1) in
	       If (p'1, p'2, p'3), w1
	   | _ ->
	       let p'1,_ = wp p1 None in
	       If (p'1, p'2, p'3), None)
    (* sequence *)
    | Seq bl -> 
	let bl',w = wp_block bl q in
	Seq bl', w
    (* function call: $\forall r. Q_f \Rightarrow q$ *)
    | App (p1, Term p2) ->
	let p'1,_ = wp p1 None in
	let p'2,_ = wp p2 None in
	App (p'1, Term p'2), None
    | App (p1, a) ->
	let p'1,_ = wp p1 None in
	App (p'1, a), None
    | Lam (bl, p) ->
	let p',w = wp p None in
	Lam (bl, p'), None
    | LetIn (x, p1, p2) ->
	failwith "todo: wp let in"
    | LetRef (x, e1, e2) ->
	let e'2, w = wp e2 q in
	let q' = optpost_app (subst_in_predicate [x, result]) w in
	let e'1,w' = wp e1 q' in
	LetRef (x, e'1, e'2), w'
    | LetRec _ ->
	failwith "todo: wp let rec"
    | While (b, invopt, (var,r), bl) ->
	d, invopt (* TODO: check *)
    | PPoint (lab, p) ->
	let p',w = wp_desc info p q in
	let w = optpost_app (erase_label lab) w in
	PPoint (lab, p'), w
    | Coerce p ->
	let p',w = wp p q in
	Coerce p', w

and wp_block bl q = match bl with
  | [] ->
      [], q
  | Statement p :: bl ->
      let bl', w = wp_block bl q in
      let p', w' = wp p w in
      Statement p' :: bl', w'
  | Label l :: bl ->
      let bl', w = wp_block bl q in
      Label l :: bl', optpost_app (erase_label l) w
  | Assert p :: bl ->
      let bl', w = wp_block bl q in
      Assert p :: bl', w

let propagate p =
  let p = normalize p in
  wp p None
