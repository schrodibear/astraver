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

(*i $Id: annot.ml,v 1.24 2004-07-02 14:45:46 filliatr Exp $ i*)

open Options
open Ident
open Misc
open Logic
open Util
open Ast
open Env
open Types

(* Automatic annotations *)

let default_post = anonymous Loc.dummy (Pvar Ident.default_post)

let is_default_post a = match a.a_value with
  | Pvar id when id == Ident.default_post -> true
  | _ -> false

(* maximum *)

let sup q q' = match q, q' with
  | None, _ ->
      q'
  | _, None ->
      q
  | Some (q, ql), Some (_, ql') ->
      assert (List.length ql = List.length ql');
      let supx (x,a) (x',a') =
	assert (x = x');
	x, if is_default_post a then a' else a
      in
      Some (q, List.map2 supx ql ql') 

(* force a post-condition *)

let force_post env q e = match q with
  | None -> 
      e
  | Some c ->
      let c = force_post_loc e.info.loc c in
      let ids = post_refs env c in
      let ef = Effect.add_reads ids e.info.kappa.c_effect in
      let k = { e.info.kappa with c_post = Some c; c_effect = ef } in
      let i = { e.info with kappa = k } in
      { e with info = i }

let post_if_none env q p = match post p with
  | None -> force_post env q p 
  | _ -> p

(* post-condition of [while b do inv I done] i.e. [I and not B] *)

let default_exns_post e =
  let xs = Effect.get_exns e in
  List.map (fun x -> x, default_post) xs
 
let while_post loc info b inv = 
  let ql = default_exns_post info.kappa.c_effect in
  match post b, inv with
    | None, None -> 
	None
    | None, Some i ->
	Some ({ a_value = i.a_value; 
		a_name = Name (post_name_from i.a_name);
		a_loc = loc }, ql)
    | Some qb, inv ->
	let _,s = decomp_boolean qb in
	let s = change_label b.info.label info.label s in
	match inv with
	  | None -> Some (anonymous loc s, ql)
	  | Some i -> Some ({ a_value = pand i.a_value s; 
			      a_name = Name (post_name_from i.a_name);
			      a_loc = loc }, ql)

let while_post_block env inv (phi,_,r) e = 
  let lab = e.info.label in
  let decphi = Papp (r, [phi; put_label_term env lab phi]) in
  let ql = default_exns_post (effect e) in
  match inv with
    | None -> 
	anonymous e.info.loc decphi, ql
    | Some i -> 
	{ a_value = pand i.a_value decphi; 
	  a_name = Name (post_name_from i.a_name);
	  a_loc = e.info.loc }, ql

let check_while_test b =
  if post b = None then begin
    wprintf b.info.loc 
      "couldn't give this test a postcondition (possible incompleteness)\n";
    if werror then exit 1
  end

(* misc. *)

let post_named c = 
  { a_value = c; a_name = Name (post_name Anonymous); a_loc = Loc.dummy }

let create_postval c = Some (post_named c)

let create_post c = Some (post_named c, [])

let is_conditional p = match p.desc with If _ -> true | _ -> false

let is_equality = function
  | Some ({ a_value = Papp (id, [Tvar t1; t2]) }, []) -> 
      id == t_eq && t1 == result
  | _ -> false

let get_equality_rhs = function
  | Some ({ a_value = Papp (id, [Tvar t1; t2]) }, []) 
    when id == t_eq && t1 == result -> t2
  | _ -> assert false

(* [extract_pre p] erase the pre-condition of [p] and returns it *)

let extract_oblig pr =
  let k = pr.info.kappa in
  { pr with info = { pr.info with 
		       obligations = []; 
		       kappa = { k with c_pre = [] } } },
  pr.info.obligations @ k.c_pre

(* adds some pre-conditions *)

let add_oblig p1 pr =
  let o = pr.info.obligations in
  { pr with info = { pr.info with obligations = o @ p1 } }

  
(* change the statement *)

let change_desc p d = { p with desc = d }

let is_bool = function
  | PureType PTbool -> true
  | _ -> false

let is_pure e = 
  let ef = effect e in 
  Effect.get_writes ef = [] && Effect.get_exns ef = []

(*s Moving obligations up in assignments *)

let lift_oblig_assign p = match p.desc with
  | Aff (x,e) ->
      let e1,p1 = extract_oblig e in
      change_desc (add_oblig p1 p) (Aff (x,e1))
  | TabAff (check, x, ({ desc = Expression _ } as e1), e2) ->
      let e1',p1 = extract_oblig e1 in
      let e2',p2 = extract_oblig e2 in
      change_desc (add_oblig (p1 @ p2) p) (TabAff (check,x,e1',e2'))
  | _ ->
      p

(*s Normalization. In this first pass, we
    (2) annotate [x := E] with [{ x = E }]
    (3) give tests the right postconditions
    (4) lift obligations up in assignements *)

let rec normalize p =
  let env = p.info.env in
  let p = lift_oblig_assign p in
  let k = p.info.kappa in
  match p.desc with
    (***
    | Expression t ->
	let t = put_label_term env p.info.label (unref_term t) in
	change_desc p (Expression t)
    ***)
    | Aff (x, ({desc = Expression t} as e1)) 
      when post e1 = None && k.c_post = None ->
	let t = put_label_term env p.info.label (unref_term t) in
	let q = create_post (equality (Tvar x) t) in
	post_if_none env q p
    | Aff (x, e1) when is_pure e1 && post e1 <> None ->
	(match post e1 with
	   | Some q1 ->
	       let q = post_app (change_label e1.info.label p.info.label) q1 in
	       let q = post_app (put_label_predicate env p.info.label) q in
	       let q = post_app (subst_in_predicate (subst_onev result x)) q in
	       post_if_none env (Some q) p
	   | _ -> assert false)
    | If (e1, e2, e3) ->
	change_desc p (If (normalize_boolean false env e1, e2, e3))
    | TabAff (_, x, ({desc=Expression t1} as e1), ({desc=Expression t2} as e2))
      when post e1 = None && post e2 = None && k.c_post = None ->
	let t1 = put_label_term env p.info.label (unref_term t1) in
	let t2 = put_label_term env p.info.label (unref_term t2) in
	let t = make_raw_store env (x, at_id x p.info.label) t1 t2 in
	let q = create_post (equality (Tvar x) t) in
	post_if_none env q p
    | While (b, invopt, var, e) ->
	let b' = normalize_boolean true env b in
	let p = match post b' with

           (* test is not annotated -> translation using an exception *)
	   | None ->
	       let effect_and_exit k = 
		 let ef = Effect.add_exn exit_exn k.c_effect in
		 let k' = type_c_of_v k.c_result_type in
		 { k' with c_effect = ef }
	       in
	       let bloc = b.info.loc in
	       let praise_exit = 
		 make_raise bloc exit_exn (PureType PTunit) env
	       in
	       let body = 
		 (* if b then e else raise Exit *)
		 make_lnode e.info.loc (If (b', e, praise_exit))
		   env [] (effect_and_exit k)
	       in
	       let d = 
		 Try 
		   (make_lnode p.info.loc
		      (While (make_annot_bool bloc true env, 
			      invopt, var, body))
		      env [] (effect_and_exit k),
		    [ (exit_exn, None), make_void p.info.loc env])
	       in
	       change_desc p d

	   (* test is annotated -> postcondition is [inv and not test] *)
	   | Some _ ->
	       (***
	       let p = change_desc p (While (b', invopt, var, e)) in
	       if post p = None then
		 let q = while_post p.info.loc p.info b' invopt in
		 force_post env q p
	       else
	       ***)
		 p
	in
	let q = optpost_app (change_label "" p.info.label) (post p) in
	force_post env q p
    | LetRef (x, ({ desc = Expression t } as e1), e2) when post e1 = None ->
	let q = create_post (equality (Tvar Ident.result) (unref_term t)) in
	change_desc p (LetRef (x, post_if_none env q e1, e2))
    | LetIn (x, ({ desc = Expression t } as e1), e2) when post e1 = None ->
	let q = create_post (equality (Tvar Ident.result) (unref_term t)) in
	change_desc p (LetIn (x, post_if_none env q e1, e2))
    | Expression _ | Var _ | Acc _ | Aff _ | TabAcc _ | TabAff _  
    | Seq _ | Lam _ | LetIn _ | LetRef _ | Rec _ | App _ 
    | Raise _ | Try _ | Absurd | Any _ ->
	p

(* [normalize_boolean b] checks if the boolean expression [b] (of type
   [bool]) is annotated; if not, tries to give it an annotation. 
   [force] indicates whether annotating is mandatory. *)

and normalize_boolean force env b =
  let k = b.info.kappa in
  let give_post b q =
    let q = option_app (force_post_loc b.info.loc) q in
    { b with info = { b.info with kappa = { k with c_post = q } } }
  in
  let q = k.c_post in
  match q with
    | Some _ ->
	(* a postcondition; nothing to do *)
	give_post b (force_bool_name q)
    | None -> begin
	match b.desc with
	  | Expression c when force ->
	      (* expression E -> result=E *)
	      let c = equality (Tvar Ident.result) (unref_term c) in
	      give_post b (create_post c)
	  | If (e1, e2, e3) ->
	      let ne1 = normalize_boolean force env e1 in
	      let ne2 = normalize_boolean force env e2 in
	      let ne3 = normalize_boolean force env e3 in
	      if is_pure e1 && is_pure e2 && is_pure e3 then
		let q1 = post ne1 in
		let q2 = post ne2 in
		let q3 = post ne3 in
		match q1, (e2.desc, q2), (e3.desc, q3) with
		  (* [a && b] *)
		  | Some q1, (_,Some q2), 
		    (Expression (Tconst (ConstBool false)),_) ->
		      let q1t,q1f = decomp_boolean q1 in
		      let q2t,q2f = decomp_boolean q2 in
		      let c = 
			Pif (Tvar Ident.result,
			     pand q1t q2t,
			     por q1f (pand q1t q2f))
		      in
		      let b' = change_desc b (If (ne1,ne2,ne3)) in
		      give_post b' (create_post c)
		  (* [a || b] *)
		  | Some q1, (Expression (Tconst (ConstBool true)),_), 
		    (_,Some q3) ->
		      let q1t,q1f = decomp_boolean q1 in
		      let q3t,q3f = decomp_boolean q3 in
		      let c = 
			Pif (Tvar Ident.result,
			     por q1t (pand q1f q3t),
			     pand q1f q3f)
		      in
		      let b' = change_desc b (If (ne1,ne2,ne3)) in
		      give_post b' (create_post c)
                  (* generic case *)
		  | Some q1, (_,Some q2), (_,Some q3) -> 
		      let q1t,q1f = decomp_boolean q1 in
		      let q2t,q2f = decomp_boolean q2 in
		      let q3t,q3f = decomp_boolean q3 in
		      let c = 
			Pif (Tvar Ident.result,
			     por (pand q1t q2t) (pand q1f q3t),
			     por (pand q1t q2f) (pand q1f q3f)) 
		      in
		      let b' = change_desc b (If (ne1,ne2,ne3)) in
		      give_post b' (create_post c)
		  | _ ->
		      b
		else 
		  b
	  | _ -> 
	      b
      end

let map_desc f p =
  let d = match p.desc with
    | Var _ 
    | Acc _ 
    | Expression _
    | Absurd
    | Any _ as d -> 
	d
    | Aff (x, e) -> 
	Aff (x, f e)
    | TabAcc (b, x, e) -> 
	TabAcc (b, x, f e)
    | TabAff (b, x, e1, e2) -> 
	TabAff (b, x, f e1, f e2)
    | Seq bl -> 
	let block_st = function
	  | Label _ | Assert _ as s -> s
	  | Statement e -> Statement (f e)
	in
	Seq (List.map block_st bl)
    | While (e1, inv, var, e2) ->
	While (f e1, inv, var, f e2)
    | If (e1, e2, e3) ->
	If (f e1, f e2, f e3)
    | Lam (bl, e) ->
	Lam (bl, f e)
    | App (e1, Term e2, k) ->
	App (f e1, Term (f e2), k)
    | App (e1, a, k) ->
	App (f e1, a, k)
    | LetRef (x, e1, e2) ->
	LetRef (x, f e1, f e2)
    | LetIn (x, e1, e2) ->
	LetIn (x, f e1, f e2)
    | Rec (x, bl, v, var, e) ->
	Rec (x, bl, v, var, f e)
    | Raise (x, Some e) ->
	Raise (x, Some (f e))
    | Raise _ as d ->
	d
    | Try (e1, eql) ->
	Try (f e1, List.map (fun (p, e) -> (p, f e)) eql)
  in
  { p with desc = d }

type pure = 
  | PureTerm of term (* result = term *)
  | PurePred of postcondition (* q(result) *)

let q_true_false q =
  let ctrue = tsubst_in_predicate (subst_one Ident.result ttrue) q in
  let cfalse = tsubst_in_predicate (subst_one Ident.result tfalse) q in
  simplify ctrue, simplify cfalse

let rec purify p =
  let a_values = List.map (fun a -> a.a_value) in
  if is_pure p then 
    let rec pure p = match p.desc with
      | Expression t when post p = None -> 
	  [],
	  equality (Tvar Ident.result) (unref_term t)
      | LetIn (x, e1, e2) when post p = None -> 
	  (* TODO: optimiser quand post1 de la forme result=E *)
	  let pre1,post1 = pure e1 in
	  let pre2,post2 = pure e2 in
	  let tyx = result_type e1 in
	  let post1_x = subst_in_predicate (subst_onev result x) post1 in
	  (* pre1 and forall x. post1(x) => pre2 *)
	  (pre1 @ [pforall x tyx (pimplies post1_x (pands pre2))]),
	  (* forall x. post1(x) => post2 *)
	  pforall x tyx (pimplies post1_x post2)
      | If (e1, e2, e3) when post p = None -> 
	  let p1,q1 = pure e1 in
	  let p2,q2 = pure e2 in
	  let p3,q3 = pure e3 in
	  let q1t,q1f = q_true_false q1 in
	  begin match e2.desc, e3.desc with
	    | _, Expression (Tconst (ConstBool false)) (* e1 && e2 *) ->
		let q2t,q2f = q_true_false q2 in
		p1 @ [pimplies q1t (pands p2)],
		Pif (Tvar Ident.result, pand q1t q2t, por q1f (pand q1t q2f))
	    | Expression (Tconst (ConstBool true)), _ (* e1 || e2 *) ->
		let q3t,q3f = q_true_false q3 in
		p1 @ [pimplies q1f (pands p3)],
		Pif (Tvar Ident.result, por q1t (pand q1f q3t), pand q1f q3f)
	    | Expression (Tconst (ConstBool false)),
	      Expression (Tconst (ConstBool true)) (* not e1 *) ->
		p1, Pif (Tvar Ident.result, q1f, q1t)
	    | _ -> 
		(* p1 and (q1(true) => p2) and (q1(false) => p3) *)
		p1 @ [pimplies q1t (pands p2); pimplies q1f (pands p3)],
		(* q1(true) and q2 or q1(false) and q3 *)
		por (pand q1t q2) (pand q1f q3)
	  end

	  (*let q2t,q2f = q_true_false q2 in
	  let q3t,q3f = q_true_false q3 in*)
	  (* if result then 
	       post1(true) and post2(true) or post1(false) and post3(true)
	     else
	       post1(true) and post2(false) or post1(false) and post3(false) *)
	  (*Pif (Tvar Ident.result,
	       por (pand q1t q2t) (pand q1f q3t),
	       por (pand q1t q2f) (pand q1f q3f))*)

      | App (e1, Term e2, k) when post p = None || post p = k.c_post ->
	  (* TODO : collecter oblig/pre de e1 et e2 *)
	  begin match k.c_post with
	    | Some (q,_) -> [], q.a_value
	    | None -> raise Exit
	  end
      | _ -> 
	  raise Exit (* we give up *)
    in
    try 
      let pre,post = pure p in
      let pre = List.map (anonymous p.info.loc) pre in
      let o = p.info.obligations @ pre in
      let c = { p.info.kappa with c_post = create_post post } in
      { p with 
	  desc = Any c; 
	  info = { p.info with obligations = o; kappa = c } }
    with Exit -> 
      map_desc purify p
  else 
    (* we apply purify recursively *) 
    map_desc purify p
