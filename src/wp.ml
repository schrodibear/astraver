(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: wp.ml,v 1.14 2002-03-05 14:41:51 filliatr Exp $ i*)

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

(* term utilities *)

let post e = e.info.kappa.c_post

(* force a post-condition *)

let update_post env top ef c =
  let i,o = Effect.get_repr ef in
  let al = 
    Idset.fold
      (fun id l -> 
	 if is_mutable_in_env env id then
	   if is_write ef id then l else (id,at_id id "") :: l
	 else if is_at id then
	   let (uid,d) = un_at id in
	   if is_mutable_in_env env uid && d = "" then 
	     (id,at_id uid top) :: l 
	   else 
	     l
	 else
	   l) 
      (predicate_vars c) []
  in
  subst_in_predicate al c
  
let force_post up env top q e =
  let ef = e.info.kappa.c_effect in
  let q' = 
    if up then option_app (named_app (update_post env top ef)) q else q 
  in
  let c' = { e.info.kappa with c_post = q' } in
  let i = { env = e.info.env; kappa = c' } in
  { desc = e.desc; info = i }

let optpost_app f = option_app (post_app f)

(* put a post-condition if none is present *)

let post_if_none_up env top q p = match p.info.kappa.c_post with
  | None -> force_post true env top q p 
  | _ -> p

let post_if_none env q p = match p.info.kappa.c_post with
  | None -> force_post false env "" q p 
  | _ -> p

let create_bool_post c =
  Some { a_value = c; a_name = Name (bool_name()) }

let is_conditional p = match p.desc with If _ -> true | _ -> false

(* [annotation_candidate p] determines if p is a candidate for a 
   post-condition *)

(*i DEAD
let annotation_candidate = function
  | { desc = If _ | LetIn _ | LetRef _ ; post = None } -> true
  | _ -> false
i*)

(* [extract_pre p] erase the pre-condition of [p] and returns it *)

let extract_pre pr =
  { desc = pr.desc; 
    info = { env = pr.info.env; kappa = { pr.info.kappa with c_pre = [] } } },
  pr.info.kappa.c_pre

(* adds some pre-conditions *)

let add_pre p1 pr =
  let k = pr.info.kappa in
  let p' = p1 @ k.c_pre in
  { desc = pr.desc; 
    info = { env = pr.info.env; kappa = { k with c_pre = p' } } }
  
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

(* [add_decreasing env inv (var,r) lab bl] adds the decreasing condition
   [phi(ren') r phi(ren)] to the last assertion of the block [bl],
   which is created if needed. *)
(*i***
let add_decreasing env inv (var,r) lab bl =
  let ids = term_now_vars env var in
  let al = Idset.fold (fun id l -> (id,at_id id lab) :: l) ids [] in
  let var_lab = subst_in_term al var in
  let dec = papplist r [var; var_lab] in
  let post = match inv with
    | None -> anonymous dec
    | Some i -> { a_value = Pand (dec, i.a_value); a_name = i.a_name }
  in
  bl @ [ Assert post ]
***i*)

(* [post_last_statement env top q bl] annotates the last statement of the
   sequence [bl] with [q] if necessary *)

(*i DEAD
let post_last_statement env top q bl =
  match List.rev bl with
    | Statement e :: rem when annotation_candidate e -> 
	List.rev ((Statement (post_if_none_up env top q e)) :: rem)
    | _ -> bl
i*)

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
	  { desc = e.desc; info = { env = env; kappa = k'} }
	else
	  change_desc p (Coerce e)
    | Debug _ | PPoint _ ->
	failwith "todo: normalize"

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

let rec wp p q =
  let env = p.info.env in
  let q = if q = None then post p else q in
  let d,w = wp_desc p.info p.desc q in
  let p = change_desc p d in
  post_if_none env q p, w

and wp_desc info d q = 
  let env = info.env in
  let result = info.kappa.c_result_name in
  match d with
    (* $wp(E,q) = q[result \leftarrow E]$ *)
    | Expression t ->
	let q = optpost_app make_before_after q in
	d, optpost_app (tsubst_in_predicate [result,t]) q
(*i    
    (* $wp(x := E, q) = q[x\leftarrow E]$ *)
    | Aff (x, { desc = Expression t }) -> 
	d, optpost_app (tsubst_in_predicate [x,t]) q
i*)
    (* $wp(x := E, q) = \forall x0. x0=E \Rightarrow q[x\leftarrow x0]$ *)
    | Aff (x, { desc = Expression t; info = ti }) -> 
	let n = Ident.bound () in
	let q = 
	  optpost_app 
	    (fun q -> 
	       let q = tsubst_in_predicate [x,Tbound n] q in
	       let ti = mlize_type ti.kappa.c_result_type in
	       Forall (x, n, ti, Pimplies (equality (Tbound n) t, q)))
	    q
	in
	d, q
    (* otherwise: $wp(x := p, q) = wp(p, q[x\leftarrow result])$ *)
    | Aff (x, p) ->
	let q' = optpost_app (subst_in_predicate [x, result]) q in
	let p',w = wp p q' in
	Aff (x, p'), w
    (* conditional: two cases depending on [p1.post] *)
    | If (p1, p2, p3) ->
	let p'2,w2 = wp p2 q in
	let p'3,w3 = wp p3 q in
	(match w2, w3, post p1 with
	   | Some {a_value=q2}, Some {a_value=q3}, Some {a_value=q1} -> 
	       (* $wp(if p1 then p2 else p3, q) = 
		  q1(true) => wp(p2, q) and q1(false) => wp(p3, q)$ *)
	       let q1 = make_before_after q1 in
	       let q1t = tsubst_in_predicate [Ident.result,ttrue] q1 in
	       let q1f = tsubst_in_predicate [Ident.result,tfalse] q1 in
	       let w = Pand (Pimplies (q1t, q2), Pimplies (q1f, q3)) in
	       If (p1, p'2, p'3), create_bool_post w
	   | Some {a_value=q2}, Some {a_value=q3}, None -> 
	       (* $wp(if p1 then p2 else p3, q) = 
		  wp(p1, if result then wp(p2, q) else wp(p3, q))$ *)
	       let result1 = p1.info.kappa.c_result_name in
	       let q1 = Pif (Tvar result1, q2, q3) in
	       let p'1,w1 = wp p1 (create_bool_post q1) in
	       If (p'1, p'2, p'3), w1
	   | _ ->
	       If (p1, p'2, p'3), None)
    (* sequence *)
    | Seq bl -> 
	let lab,bl = top_point_block bl in
	let q = optpost_app (change_label "" lab) q in
	let bl',w = wp_block bl q in
	Seq bl', w
    (* function call: $\forall r. Q_f \Rightarrow q$ *)
    | App _ ->
	let w = wp_app info q in
	d, w
    | Lam (bl, p) ->
	let env' = traverse_binders env bl in
	let p',w = wp p None in
	Lam (bl, p'), None
    | LetRef (x, e1, e2) ->
	let e'2, w = wp e2 q in
	let q' = optpost_app (subst_in_predicate [x, result]) w in
	let e'1,w' = wp e1 q' in
	LetRef (x, e'1, e'2), w'
    | While (b, invopt, (var,r), bl) ->
	d, invopt
    | _ -> 
	failwith "todo wp"

(*i TODO: FAUX il faut quantifier également par rapport aux variables 
    modifiées par l'appel i*)
and wp_app info q =
  optpost_app 
    (fun q -> 
       let n = Ident.bound () in
       let q = make_before_after q in
       let q = tsubst_in_predicate [Ident.result,Tbound n] q in
       let ti = mlize_type info.kappa.c_result_type in
       let rname = info.kappa.c_result_name in
       match info.kappa.c_post with
	 | Some qf -> 
	     let qf = tsubst_in_predicate [rname,Tbound n] qf.a_value in
	     Forall (rname, n, ti, Pimplies (qf, q))
	 | None ->
	     Forall (rname, n, ti, q))
    q

and wp_block bl q = match bl with
  | [] ->
      [], optpost_app make_before_after q
  | Statement p :: bl ->
      let bl', w = wp_block bl q in
      let w = if is_conditional p && post p <> None then post p else w in
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
  let p,_ = wp p None in
  p

