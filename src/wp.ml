
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: wp.ml,v 1.3 2001-08-21 20:57:02 filliatr Exp $ *)

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
  { desc = e.desc; pre = e.pre; post = q'; loc = e.loc; info = i }

let optpost_app f = option_app (post_app f)

(* put a post-condition if none is present *)

let post_if_none_up env top q = function
(*i
  | { post = None; desc = Aff (x, { desc = Expression t }) } as p -> 
      let t = make_after_before_term env t in
      let q =
	optpost_app (fun q -> Pimplies (Pterm (Tapp (t_eq, [Tvar x;t])), q)) q
      in
      force_post true env top q p 
i*)
  | { post = None } as p -> 
      force_post true env top q p 
  | p -> 
      p

let post_if_none env q = function
  | { post = None } as p -> force_post false env "" q p 
  | p -> p

let create_bool_post c =
  Some { a_value = c; a_name = Name (bool_name()) }

let is_conditional p = match p.desc with If _ -> true | _ -> false

(* [annotation_candidate p] determines if p is a candidate for a 
 * post-condition *)

let annotation_candidate = function
  | { desc = If _ | LetIn _ | LetRef _ ; post = None } -> true
  | _ -> false

(* [extract_pre p] erase the pre-condition of p and returns it *)

let extract_pre pr =
  { desc = pr.desc; pre = []; post = pr.post; loc = pr.loc;
    info = { env = pr.info.env; kappa = { pr.info.kappa with c_pre = [] } } },
  pr.info.kappa.c_pre

(* adds some pre-conditions *)

let add_pre p1 pr =
  let k = pr.info.kappa in
  let p' = p1 @ k.c_pre in
  { desc = pr.desc; pre = p'; post = pr.post; loc = pr.loc;
    info = { env = pr.info.env; kappa = { k with c_pre = p' } } }
  
(* change the statement *)

let change_desc p d = { p with desc = d }

(* [normalize_boolean b] checks if the boolean expression b (of type bool) is 
 * annotated, and if it is not the case tries to add the annotation
 * (if result then c=true else c=false) if b is an expression c.
 *)

let is_bool = function
  | PureType PTbool -> true
  | _ -> false

(*i
let result_eq_true = 
  Pterm (Tapp (t_eq, [Tvar result; Tconst (ConstBool true)]))

let result_eq_false = 
  Pterm (Tapp (t_eq, [Tvar result; Tconst (ConstBool false)]))

let spec_and r1 s1 r2 s2 =
  Pand (Pimplies (result_eq_true, Pand (r1, r2)),
	Pimplies (result_eq_false, Por (s1, s2)))

let spec_or r1 s1 r2 s2 =
  Pand (Pimplies (result_eq_true, Por (r1, r2)),
	Pimplies (result_eq_false, Pand (s1, s2)))

let spec_not r s =
  Pand (Pimplies (result_eq_true, s), Pimplies (result_eq_false, r))
i*)

(* top point of a program *)

let top_point = function
  | PPoint (s,_) as p -> s,p
  | p -> let s = label_name () in s, PPoint(s,p)

let top_point_block = function
  | (Label s :: _) as b -> s,b
  | b -> let s = label_name () in s, (Label s)::b

(* [add_decreasing env ren ren' phi r bl] adds the decreasing condition
 *    phi(ren') r phi(ren)
 * to the last assertion of the block [bl], which is created if needed
 *)

let add_decreasing env inv (var,r) lab bl =
  let ids = term_now_vars env var in
  let al = Idset.fold (fun id l -> (id,at_id id lab) :: l) ids [] in
  let var_lab = subst_in_term al var in
  let dec = Pterm (applist r [var;var_lab]) in
  let post = match inv with
    | None -> anonymous dec
    | Some i -> { a_value = Pand (dec, i.a_value); a_name = i.a_name }
  in
  bl @ [ Assert post ]

(* [post_last_statement env top q bl] annotates the last statement of the
 * sequence bl with q if necessary *)

let post_last_statement env top q bl =
  match List.rev bl with
    | Statement e :: rem when annotation_candidate e -> 
	List.rev ((Statement (post_if_none_up env top q e)) :: rem)
    | _ -> bl

(* [propagate_desc] moves the annotations inside the program 
 * [info] is the typing information coming from the outside annotations *)

(*i
let rec propagate_desc ren info d = 
  let env = info.env in
  let p = info.kappa.c_pre in
  let q = info.kappa.c_post in
  match d with
    | If (e1,e2,e3) ->
      (* propagation number 2 *)
	let e1' = normalize_boolean ren env (propagate ren e1) in
	if e2.post = None || e3.post = None then
	  let top = label_name() in
	  let ren' = push_date ren top in
	  PPoint (top, If (e1', 
			   propagate ren' (post_if_none_up env top q e2),
			   propagate ren' (post_if_none_up env top q e3)))
	else
	  If (e1', propagate ren e2, propagate ren e3)
    | Aff (x,e) ->
      	Aff (x, propagate ren e)
    | TabAcc (ch,x,e) ->
      	TabAcc (ch, x, propagate ren e)
    | TabAff (ch,x,({desc=Expression c} as e1),e2) ->
	let p = make_pre_access ren env x c in
	let e1' = add_pre [(anonymous_pre true p)] e1 in
      	TabAff (false, x, propagate ren e1', propagate ren e2)
    | TabAff (ch,x,e1,e2) ->
      	TabAff (ch, x, propagate ren e1, propagate ren e2)
    | App (f,l) ->
      	App (propagate ren f, List.map (propagate_arg ren) l)
    | SApp (f,l) ->
	let l = 
	  List.map (fun e -> normalize_boolean ren env (propagate ren e)) l
	in
      	SApp (f, l)
    | Lam (bl,e) ->
      	Lam (bl, propagate ren e)
    | Seq bl ->
	let top,bl = top_point_block bl in
	let bl = post_last_statement env top q bl in
      	Seq (propagate_block ren env bl)
    | While (b,inv,var,bl) ->
	let b = normalize_boolean ren env (propagate ren b) in
	let lab,bl = top_point_block bl in
	let bl = add_decreasing env inv var lab bl in
      	While (b,inv,var,propagate_block ren env bl)
    | LetRef (x,e1,e2) ->
	let top = label_name() in
	let ren' = push_date ren top in
	PPoint (top, LetRef (x, propagate ren' e1, 
	      		     propagate ren' (post_if_none_up env top q e2)))
    | LetIn (x,e1,e2) ->
	let top = label_name() in
	let ren' = push_date ren top in
      	PPoint (top, LetIn (x, propagate ren' e1, 
			    propagate ren' (post_if_none_up env top q e2)))
    | LetRec (f,bl,v,var,e) ->
      	LetRec (f, bl, v, var, propagate ren e)
    | PPoint (s,d) -> 
      	PPoint (s, propagate_desc ren info d)
    | Debug _ | Var _ 
    | Acc _ | Expression _ as d -> d
	  

(* [propagate] adds new annotations if possible *)
and propagate ren p =
  let env = p.info.env in
  let p = match p.desc with
    | App (f,l) ->
	let _,(_,so,ok),capp = effect_app ren env f l in
	let qapp = capp.c_post in
	if ok then
	  let q = option_app (named_app (tsubst_in_predicate so)) qapp in
	  post_if_none env q p
	else
	  p
    | _ -> p
  in
  let d = propagate_desc ren p.info p.desc in
  let p = change_desc p d in
  match d with
    | Aff (x,e) ->
	let e1,p1 = extract_pre e in
	change_desc (add_pre p1 p) (Aff (x,e1))

    | TabAff (check, x, ({ desc = Expression _ } as e1), e2) ->
	let e1',p1 = extract_pre e1 in
	let e2',p2 = extract_pre e2 in
	change_desc (add_pre (p1@p2) p) (TabAff (check,x,e1',e2'))

    | While (b,inv,_,_) ->
	let _,s = decomp_boolean b.post in
	let s = make_before_after s in
	let q = match inv with
	    None -> Some (anonymous s)
	  | Some i -> Some { a_value = Pand (i.a_value, s); a_name = i.a_name }
	in
	(*i let q = option_app (named_app abstract_unit) q in i*)
	post_if_none env q p

    | SApp ([Var id], [e1;e2]) when id == p_and || id == p_or ->
	let q1 = e1.info.kappa.c_post 
	and q2 = e2.info.kappa.c_post in
	let (r1,s1) = decomp_boolean q1
	and (r2,s2) = decomp_boolean q2 in
	let q =
	  let c = (if id == p_and then spec_and else spec_or) r1 s1 r2 s2 in
	  create_bool_post c
	in
	post_if_none env q p

    | SApp ([Var id], [e1]) when id == p_not ->
	let q1 = e1.info.kappa.c_post in
	let (r1,s1) = decomp_boolean q1 in
	let q = create_bool_post (spec_not r1 s1) in
	post_if_none env q p

    | _ -> p

and propagate_arg ren = function
  | Type _ | Refarg _ as a -> a
  | Term e -> Term (propagate ren e)


and propagate_block ren env = function 
  | [] -> 
      []
  | (Statement p) :: (Assert q) :: rem when annotation_candidate p ->
      let q' =
	(*i let ((id,v),_,_,_) = p.info.kappa in
	let tv = Monad.trad_ml_type_v ren env v in
	named_app (abstract [id,tv]) i*) q
      in
      let p' = post_if_none env (Some q') p in
      (Statement (propagate ren p')) :: (Assert q) 
      :: (propagate_block ren env rem)
  | (Statement p) :: rem ->
      (Statement (propagate ren p)) :: (propagate_block ren env rem)
  | (Label s as x) :: rem ->
      x :: propagate_block (push_date ren s) env rem
  | x :: rem ->
      x :: propagate_block ren env rem
i*)

(*s Normalization. In this first pass, we
    (1) annotate the function calls
    (2) annotate x := E with { x = E }
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

let rec normalize ren p =
  let env = p.info.env in
  let p = lift_pre p in
  match p.desc with
    | App (f,l) ->
	let _,(_,so,ok),capp = effect_app ren env f l in
	let qapp = capp.c_post in
	if ok then
	  let q = optpost_app (tsubst_in_predicate so) qapp in
	  post_if_none env q p
	else
	  p
    | Aff (x, { desc = Expression t }) when p.post = None ->
	let t = make_after_before_term env t in
	let q = create_bool_post (Pterm (Tapp (t_eq, [Tvar x;t]))) in
	post_if_none env q p
    | If (e1, e2, e3) ->
	change_desc p (If (normalize_boolean ren env e1, 
			   normalize ren e2, normalize ren e3))
(*i
    | Expression t ->
	let t = make_after_before_term env t in
	let c = Pterm (Tapp (t_eq, [Tvar Ident.result; t])) in
	post_if_none env (create_bool_post c) p
i*)
    | Seq bl ->
	change_desc p (Seq (normalize_block ren bl))
    | Lam (bl,e) ->
	let env' = traverse_binders env bl in
	let ren' = initial_renaming env' in
	change_desc p (Lam (bl, normalize ren' e))
    | _ -> p

and normalize_block ren = function
  | [] ->
      []
  | Statement p :: bl ->
      let p' = normalize ren p in
      let efp = p.info.kappa.c_effect in
      let ren' = next ren (get_writes efp) in
      let bl' = normalize_block ren' bl in
      Statement p' :: bl'
  | Label l :: bl ->
      let ren' = push_date ren l in
      let bl' = normalize_block ren' bl in
      Label l :: bl'
  | Assert p :: bl ->
      let bl' = normalize_block ren bl in
      Assert p :: bl'

and normalize_boolean ren env b =
  let k = b.info.kappa in
  Error.check_no_effect b.loc k.c_effect;
  let give_post b q =
    { b with post = q; info = { b.info with kappa = { k with c_post = q } } }
  in
  if is_bool k.c_result_type then
    let q = k.c_post in
    match q with
      | Some _ ->
	  (* a postcondition; nothing to do *)
	  normalize ren (give_post b (force_bool_name q))
      | None -> begin
	  (* nothing *)
	  match b.desc with
	    | Expression c ->
		(* expression E -> if result then E else not E *)
		let c = Pif (Pterm (Tvar Ident.result), 
			     Pterm c, Pnot (Pterm c)) in
		give_post b (create_bool_post c)
	    | If (e1, e2, e3) ->
		let ne1 = normalize_boolean ren env e1 in
		let ne2 = normalize_boolean ren env e2 in
		let ne3 = normalize_boolean ren env e3 in
		let q1t,q1f = decomp_boolean ne1.post in
		let q2t,q2f = decomp_boolean ne2.post in
		let q3t,q3f = decomp_boolean ne3.post in
		let c = Pif (Pterm (Tvar Ident.result),
			     por (pand q1t q2t) (pand q1f q3t),
			     por (pand q1t q2f) (pand q1f q3f)) in
		let b' = change_desc b (If (ne1,ne2,ne3)) in
		give_post b' (create_bool_post c)
	    | _ -> 
		let b = normalize ren b in
		assert (b.post <> None);
		normalize_boolean ren env b
	end
  else
    Error.should_be_boolean b.loc

(*s WP. [wp ren p q] computes the weakest precondition [wp(p,q)]
    and gives postcondition [q] to [p] if necessary. *)

let rec wp ren p q =
  let env = p.info.env in
  let q = if q = None then p.post else q in
  let d,w = wp_desc ren p.info p.desc q in
  let p = change_desc p d in
  post_if_none env q p, w

and wp_desc ren info d q = 
  let env = info.env in
  let result = info.kappa.c_result_name in
  match d with
    (* $wp(E,q) = q[result \leftarrow E]$ *)
    | Expression t ->
	d, optpost_app (tsubst_in_predicate [result,t]) q
    (* $wp(x := E, q) = q[x\leftarrow E]$ *)
(*i    
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
	       Forall (x,n,ti,Pimplies (Pterm (Tapp (t_eq,[Tbound n;t])), q))) 
	    q
	in
	d, q
    (* otherwise: $wp(x := p, q) = wp(p, q[x\leftarrow result])$ *)
    | Aff (x, p) ->
	let q' = optpost_app (subst_in_predicate [x, result]) q in
	let p',w = wp ren p q' in
	Aff (x, p'), w
    (* $wp(if p1 then p2 else p3, q) = 
        wp(p1, if result then wp(p2, q) else wp(p3, q))$ *)
    | If (p1, p2, p3) ->
	let p'2,w2 = wp ren p2 q in
	let p'3,w3 = wp ren p3 q in
	let q' = match w2, w3 with
	  | Some q2, Some q3 -> 
	      let result1 = p1.info.kappa.c_result_name in
	      let q = Pif (Pterm (Tvar result1), q2.a_value, q3.a_value) in
	      create_bool_post q
	  | _ ->
	      None
	in
	let p'1,w1 = wp ren p1 q' in
	If (p'1, p'2, p'3), w1
    (* sequence *)
    | Seq bl -> 
	let lab,bl = top_point_block bl in
	let q = optpost_app (change_label "" lab) q in
	let bl',w = wp_block ren bl q in
	Seq bl', w
    (* function call: $\forall r. Q_f \Rightarrow q$ *)
    | App _ ->
	let w = wp_app info q in
	d, w
    | Lam (bl, p) ->
	let env' = traverse_binders env bl in
	let ren' = initial_renaming env' in
	let p',w = wp ren' p None in
	Lam (bl, p'), None
    (* Other cases... *)
    | _ -> 
	failwith "todo wp"

and wp_app info q =
  optpost_app 
    (fun q -> 
       let n = Ident.bound () in
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

and wp_block ren bl q = match bl with
  | [] ->
      [], optpost_app make_before_after q
  | Statement p :: bl ->
      let efp = p.info.kappa.c_effect in
      let ren' = next ren (get_writes efp) in
      let bl', w = wp_block ren' bl q in
      let w = if is_conditional p && p.post <> None then p.post else w in
      let p', w' = wp ren p w in
      Statement p' :: bl', w'
  | Label l :: bl ->
      let ren' = push_date ren l in
      let bl', w = wp_block ren' bl q in
      Label l :: bl', optpost_app (erase_label l) w
  | Assert p :: bl ->
      let bl', w = wp_block ren bl q in
      Assert p :: bl', w

let propagate ren p =
  let p = normalize ren p in
  let p,_ = wp ren p None in
  p

