(* Certification of Imperative Programs / Jean-Christophe Filli�tre *)

(*i $Id: wp.ml,v 1.58 2002-10-11 15:05:03 filliatr Exp $ i*)

open Format
open Ident
open Error
open Logic
open Misc
open Types
open Ast
open Util
open Env
open Effect
open Rename

(* force a post-condition *)

let force_post env q e = match q with
  | None -> 
      e
  | Some c ->
      let ids = post_refs env c in
      let ef = Effect.add_reads ids e.info.kappa.c_effect in
      let k = { e.info.kappa with c_post = q; c_effect = ef } in
      let i = { e.info with kappa = k } in
      { desc = e.desc; info = i }

let post_if_none env q p = match post p with
  | None -> force_post env q p 
  | _ -> p

(* post-condition of [while b do inv I done] i.e. [I and not B] *)

let while_post info b inv = 
  let _,s = decomp_boolean (post b) in
  let s = change_label b.info.label info.label s in
  match inv with
    | None -> Some (anonymous s, [])
    | Some i -> Some ({ a_value = pand i.a_value s; 
			a_name = Name (post_name_from i.a_name) }, [])

let while_post_block env inv (phi,_,r) e = 
  let lab = e.info.label in
  let decphi = Papp (r, [phi; put_label_term env lab phi]) in
  match inv with
    | None -> 
	(anonymous decphi, [])
    | Some i -> 
	({ a_value = pand i.a_value decphi; 
	   a_name = Name (post_name_from i.a_name) }, [])

(* misc. *)

let post_named c = { a_value = c; a_name = Name (post_name Anonymous) }

let create_postval c = Some (post_named c)

let create_post c = Some (post_named c, [])

let is_conditional p = match p.desc with If _ -> true | _ -> false

(* [extract_pre p] erase the pre-condition of [p] and returns it *)

let extract_pre pr =
  { desc = pr.desc; 
    info = { pr.info with kappa = { pr.info.kappa with c_pre = [] } } },
  pr.info.kappa.c_pre

(* adds some pre-conditions *)

let add_pre p1 pr =
  let k = pr.info.kappa in
  let p' = k.c_pre @ p1 in
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
    | Aff (x, ({desc = Expression t} as e1)) 
      when post e1 = None && k.c_post = None ->
	let t = put_label_term env p.info.label t in
	let q = create_post (equality (Tvar x) t) in
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
    | TabAff (_, x, ({desc=Expression t1} as e1), ({desc=Expression t2} as e2))
      when post e1 = None && post e2 = None && k.c_post = None ->
	let t1 = put_label_term env p.info.label t1 in
	let t2 = put_label_term env p.info.label t2 in
	let t = make_raw_store env (x, at_id x p.info.label) t1 t2 in
	let q = create_post (equality (Tvar x) t) in
	post_if_none env q p
    | TabAff (b, x, e1, e2) ->
	change_desc p (TabAff (b, x, normalize e1, normalize e2))
    | Seq bl ->
	change_desc p (Seq (normalize_block bl))
    | Lam (bl, e) ->
	change_desc p (Lam (bl, normalize e))
    | While (b, invopt, var, e) ->
	let b' = normalize_boolean env b in
	let p = change_desc p (While (b', invopt, var, normalize e)) in
	(match post p with
	   | None -> 
	       let q = while_post p.info b' invopt in
	       force_post env q p
	   | Some q ->
	       let q = post_app (change_label "" p.info.label) q in
	       force_post env (Some q) p)
    | LetRef (x, ({ desc = Expression t } as e1), e2) when post e1 = None ->
	let q = create_post (equality (Tvar Ident.result) t) in
	change_desc p (LetRef (x, post_if_none env q e1, normalize e2))
    | LetRef (x, e1, e2) ->
	change_desc p (LetRef (x, normalize e1, normalize e2))
    | LetIn (x, ({ desc = Expression t } as e1), e2) when post e1 = None ->
	let q = create_post (equality (Tvar Ident.result) t) in
	change_desc p (LetIn (x, post_if_none env q e1, normalize e2))
    | LetIn (x, e1, e2) ->
	change_desc p (LetIn (x, normalize e1, normalize e2))
    | Rec (x, bl, v, var, e1) ->
	change_desc p (Rec (x, bl, v, var, normalize e1))
    | App (e1, Term e2, k) ->
	change_desc p (App (normalize e1, Term (normalize e2), k))
    | App (e1, (Refarg _ as r), k) ->
	change_desc p (App (normalize e1, r, k))
    | App (e1, Type v, k) ->
	change_desc p (App (normalize e1, Type v, k))
    | Raise (id, po) ->
	change_desc p (Raise (id, option_app normalize po))
    | Try (e, hl) ->
	change_desc p (Try (normalize e, 
			    List.map (fun (p,e) -> (p, normalize e)) hl))

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
	      (* expression E -> result=E *)
	      let c = equality (Tvar Ident.result) c in
	      give_post b (create_post c)
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
	      give_post b' (create_post c)
	  | _ -> 
	      normalize b
      end

let output p = 
  let w = Effect.get_writes (effect p) in
  let env = p.info.env in
  List.map (fun id -> (id, type_in_env env id)) w

(*s [filter_post k q] removes exc. postconditions from [q] which do not
    appear in typing info [k] *)

let filter_post k =
  let ef = k.kappa.c_effect in
  let keep (x,_) = is_exn ef x in
  option_app (fun (q, ql) -> (q, List.filter keep ql))

(*s [saturate_post k a q] makes a postcondition for a program of type [k]
    out of a normal postcondition [a] and the exc. postconditions from [q] *)

let saturate_post k a q = 
  let ql = match q with Some (_,l) -> l | None -> [] in
  let set_post x = x, try List.assoc x ql with Not_found -> anonymous Ptrue in
  let xs = get_exns k.kappa.c_effect in
  let saturate a = (a, List.map set_post xs) in
  option_app saturate a


(*s WP. [wp p q] computes the weakest precondition [wp(p,q)]
    and gives postcondition [q] to [p] if necessary.

    wp: typed_program -> postcondition option -> assertion option *)

let rec wp p q =
  let env = p.info.env in
  let lab = p.info.label in
  let postp = post p in
  let q0 = if postp = None then q else postp in
  let q0 = optpost_app (change_label "" lab) q0 in
  let d,w = wp_desc p.info p.desc q0 in
  let p = change_desc p d in
  let w = option_app (named_app (erase_label lab)) w in
  let p = if postp = None then force_post env q0 p else p in
  let w = match postp, q with
    | Some ({a_value=q'}, []), Some ({a_value=q}, []) ->
	let vars = (result, result_type p) :: (output p) in
	let w = foralls vars (Pimplies (q', q)) in
	Some (anonymous (erase_label lab w))
    | Some _, Some _ ->
	assert false
    | _ -> 
	w
  in
  p, w

and wp_desc info d q = 
  let result = info.kappa.c_result_name in
  match d with
    (* TODO: check if likely *)
    | Var x ->
	let w = optpost_val q in
	d, optnamed_app (tsubst_in_predicate (subst_one result (Tvar x))) w
    (* $wp(E,q) = q[result \leftarrow E]$ *)
    | Expression t ->
	let w = optpost_val q in
	d, optnamed_app (tsubst_in_predicate (subst_one result t)) w
    (* $wp(!x,q) = q[result \leftarrow x]$ *)
    | Acc x ->
	let w = optpost_val q in
	d, optnamed_app (subst_in_predicate (subst_onev result x)) w
    (* $wp(x := e, q) = wp(e, q[result\leftarrow void; x\leftarrow result])$ *)
    | Aff (x, p) ->
	let q = optval_app (tsubst_in_predicate (subst_one result tvoid)) q in
	let q = optval_app (subst_in_predicate (subst_onev x result)) q in
	let p',w = wp p q in
	Aff (x, p'), w
    | TabAcc (ck, x, e1) ->
	let t = make_raw_access info.env (x,x) (Tvar result) in
	let q = optpost_app (tsubst_in_predicate (subst_one result t)) q in
	let e'1,w = wp e1 q in
	TabAcc (ck, x, e'1), w
    | TabAff (ck, x, e1, e2) ->
	(* TODO: does not propagate inside [e1] *)
	let q = optpost_app (tsubst_in_predicate (subst_one result tvoid)) q in
	let v = fresh_var () in
	let st = make_raw_store info.env (x,x) (Tvar result) (Tvar v) in
	let q1 = optpost_app (tsubst_in_predicate (subst_one x st)) q in
	let q1 = filter_post e1.info q1 in
	let _,w1 = wp e1 q1 in
	let e'1,_ = wp e1 None in
	let w1 = optnamed_app (subst_in_predicate (subst_onev v result)) w1 in
	let q2 = saturate_post e2.info w1 q in
	let e'2,w2 = wp e2 q2 in
	TabAff (ck, x, e'1, e'2), w2
    (* conditional: two cases depending on [p1.post] *)
    | If (p1, p2, p3) ->
	let p'2,w2 = wp p2 (filter_post p2.info q) in
	let p'3,w3 = wp p3 (filter_post p3.info q) in
	(match w2, w3, post p1 with
	   | Some {a_value=q2}, Some {a_value=q3}, _ -> 
	       (* $wp(if p1 then p2 else p3, q) = 
		  wp(p1, if result then wp(p2, q) else wp(p3, q))$ *)
	       let result1 = p1.info.kappa.c_result_name in
	       let q1 = create_postval (Pif (Tvar result1, q2, q3)) in
	       let q1 = saturate_post p1.info q1 q in
	       let p'1,w1 = wp p1 q1 in
	       If (p'1, p'2, p'3), w1
	   | _ ->
	       let p'1,_ = wp p1 None in
	       If (p'1, p'2, p'3), None)
    | Seq bl -> 
	let bl',w = wp_block bl q in
	Seq bl', w
    | App (p1, Term p2, k) ->
	let p'1,_ = wp p1 None in
	let p'2,_ = wp p2 None in
	App (p'1, Term p'2, k), None
    | App (p1, a, k) ->
	let p'1,_ = wp p1 None in
	App (p'1, a, k), None
    | Lam (bl, p) ->
	let p',_ = wp p None in
	Lam (bl, p'), None
    | LetIn (x, _, _) | LetRef (x, _, _) when occur_post x q ->
        Report.raise_unlocated 
	  (AnyMessage ("cannot compute wp due to capture variable;\n" ^
                       "please rename variable " ^ Ident.string x))
    | LetIn (x, e1, e2) ->
	let e'2, w2 = wp e2 (filter_post e2.info q) in
	let q1 = optnamed_app (subst_in_predicate (subst_onev x result)) w2 in
	let q1 = saturate_post e1.info q1 q in
	let e'1,w = wp e1 q1 in
	LetIn (x, e'1, e'2), w
    | LetRef (x, e1, e2) ->
	(* same as LetIn: correct? *)
	let e'2, w2 = wp e2 (filter_post e2.info q) in
	let q1 = optnamed_app (subst_in_predicate (subst_onev x result)) w2 in
	let q1 = saturate_post e1.info q1 q in
	let e'1,w = wp e1 q1 in
	LetRef (x, e'1, e'2), w
    | Rec (f, bl, v, var, e) ->
	let e',_ = wp e None in
	Rec (f, bl, v, var, e'), None
    | While (b, inv, var, e) ->
	let b',_ = wp b None in
	let q = while_post_block info.env inv var e in
	let e',_ = wp e (Some q) in
	While (b', inv, var, e'), None
    (* $wp(raise E, _, R) = R$ *)
    | Raise (id, None) ->
	d, option_app (fun (_,ql) -> List.assoc id ql) q
    (* $wp(raise (E e), _, R) = wp(e, R, R)$ *)
    | Raise (id, Some e) ->
	let make_post (_,ql) = let r = List.assoc id ql in (r, ql) in
	let qe = filter_post e.info (option_app make_post q) in
	let e',w = wp e qe in
	Raise (id, Some e'), w
    (* $wp(try e1 with E -> e2, Q, R) = wp(e1, Q, wp(e2, Q, R))$ *)
    | Try (e, hl) ->
	let subst w = function
	  | None -> w
	  | Some x -> optnamed_app (subst_in_predicate (subst_onev x result)) w
	in
	let hl' = 
	  List.map (fun ((x,v) as p, h) -> 
		      let h',w = wp h (filter_post h.info q) in
		      (p,h'), (x, subst w v)) hl 
	in
	let hl',hwl = List.split hl' in
	let make_post (q,ql) = 
	  let hpost (x,r) =
	    x, try (match List.assoc x hwl with None -> r | Some w -> w)
	       with Not_found -> r
	  in
	  (q, List.map hpost ql)
	in
	let q = saturate_post e.info (option_app fst q) q in
	let qe = filter_post e.info (option_app make_post q) in
	let e',w = wp e qe in
	Try (e', hl'), w

and wp_block bl q = match bl with
  | [] ->
      [], option_app post_val q
  | Statement p :: bl ->
      let bl', w = wp_block bl q in
      let w = saturate_post p.info w q in
      let p', w' = wp p w in
      Statement p' :: bl', w'
  | Label l :: bl ->
      let bl', w = wp_block bl q in
      Label l :: bl', optnamed_app (erase_label l) w
  | Assert p :: bl ->
      let bl', w = wp_block bl q in
      Assert p :: bl', optnamed_app (fun c -> pand p.a_value c) w

let propagate p =
  let p = normalize p in
  wp p None
