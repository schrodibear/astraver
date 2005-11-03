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

(*i $Id: purify.ml,v 1.2 2005-11-03 14:11:37 filliatr Exp $ i*)

open Ident
open Logic
open Util
open Ast
open Env
open Misc
open Types

let is_result_eq = function
  | Papp (id, [Tvar id'; t], _) when is_eq id && id' == result -> Some t
  | _ -> None

let is_pure e = 
  let ef = effect e in 
  Effect.get_writes ef = [] && Effect.get_exns ef = []

let make_post loc p =
  { a_name = post_name (); a_value = p; a_loc = loc; a_proof = None }, []

let set_post p q = force_post p.info.t_env (Some q) p

let get_post p = match p.info.t_post with
  | None -> assert false
  | Some (q,_) -> q

let make_node p d q =
  { p with desc = d; info = { p.info with t_post = Some (q,[]) } }

let q_true_false q =
  let ctrue = tsubst_in_predicate (subst_one Ident.result ttrue) q in
  let cfalse = tsubst_in_predicate (subst_one Ident.result tfalse) q in
  simplify ctrue, simplify cfalse

type purity =
  | Pure of Ast.assertion list * term option (* post is result = term *)
  | Impure

let get_pre = function
  | Pure (p, _) -> p
  | Impure -> [] (* assert false ? *)

let put_pre e p = { e with desc = Assertion (get_pre p, e) }

let purity l q = Pure (l, is_result_eq q)

(* [purify p = p',r] has the following invariants: 
   - r = Pure or r = PureEq => p is side-effects free and p' has a post
   - r = PureEq t => p' post is result=t 
 *)

(****
let rec purify p =
  let pre_named = pre_named p.info.t_loc in
  let post_named = post_named p.info.t_loc in
  let impure d = { p with desc = d }, Impure in
  match p.desc with
    | Expression t -> 
	begin match post p with
	  | None ->
	      let t = unref_term t in
	      let q = tequality (result_type p) (Tvar Ident.result) t in
	      set_post p (make_post p.info.t_loc q), Pure ([], Some t)
	  | Some (q,_) -> 
	      p, purity [] q.a_value
	 end
    | Assertion (l, e) ->
	begin match purify e with
	  | e, Impure -> { p with desc = Assertion (l, e) }, Impure
	  | e, Pure (l', t) -> e, Pure (l @ l', t)
	end
    | LetIn (x, e1, e2) -> 
	let e1,p1 = purify e1 in
	let e2,p2 = purify e2 in
	if p1 = Impure || p2 = Impure then
	  impure (LetIn (x, put_pre e1 p1, put_pre e2 p2))
	else 
	  let q,pur =
	    let post1 = get_post e1 in
	    let post2 = get_post e2 in
	    match p1, p2 with
	      | Pure (o1, Some t1), Pure (o2, t2) ->
		  let s = subst_one x t1 in
		  let sp = tsubst_in_predicate s in
		  let o = o1 @ (List.map (asst_app sp) o2) in
		  asst_app sp post2,
		  Pure (o, option_app (tsubst_in_term s) t2)
	      | Pure (o1, None), Pure (o2, _) ->
		  let tyx = result_type e1 in
		  let s = subst_in_predicate (subst_onev result x) in
		  let post1_x = s post1.a_value in
		  let o =
		    (* pre1 and (forall x. post1(x) => pre2) *)
		    pforall x tyx (pimplies post1_x (pands (a_values o2))) 
		  in
		  let q = 
		    (* exists x. post1(x) and post2 *)
		    pexists x tyx (pand post1_x post2.a_value)
		  in
		  post_named q, Pure (o1 @ [pre_named o], None)
	      | Impure, _ | _, Impure -> assert false
	  in
	  begin match post p with 
            | None -> 
		make_node p (LetIn (x, e1, e2)) q, pur
	    | Some (q,_) -> 
		{ p with desc = (LetIn (x, e1, e2)) }, 
		purity (get_pre pur) q.a_value
	  end
    | If (e1, e2, e3) ->
	let e1,p1 = purify e1 in
	let e2,p2 = purify e2 in
	let e3,p3 = purify e3 in
	if p1 = Impure || p2 = Impure || p3 = Impure then 
	  impure (If (put_pre e1 p1, put_pre e2 p2, put_pre e3 p3))
	else 
	  let q,pur = 
	    let o1,q1 = get_pre p1, get_post e1 in
	    let o2,q2 = get_pre p2, get_post e2 in
	    let o3,q3 = get_pre p3, get_post e3 in
	    let q1t,q1f = q_true_false q1.a_value in
	    match e2.desc, e3.desc with
	      | _, Expression (Tconst (ConstBool false)) (* e1 && e2 *) ->
		  let q2t,q2f = q_true_false q2.a_value in
		  let o = pimplies q1t (pands (a_values o2)) in
		  let q =
		    Pif (Tvar Ident.result, 
			 pand q1t q2t, por q1f (pand q1t q2f))
		  in
		  post_named q, Pure (o1 @ [pre_named o], None)
	      | Expression (Tconst (ConstBool true)), _ (* e1 || e2 *) ->
		  let q3t,q3f = q_true_false q3.a_value in
		  let o =  pimplies q1f (pands (a_values o3)) in
		  let q = 		
		    Pif (Tvar Ident.result, 
			 por q1t (pand q1f q3t), pand q1f q3f)
		  in
		  post_named q, Pure (o1 @ [pre_named o], None)
	      | Expression (Tconst (ConstBool false)),
		Expression (Tconst (ConstBool true)) (* not e1 *) ->
		  post_named (Pif (Tvar Ident.result, q1f, q1t)), 
		  Pure (o1, None)
	      | _ -> 
		  let o = 
		    (* p1 and (q1(true) => p2) and (q1(false) => p3) *)
		    pands 
		      [pimplies q1t (pands (a_values o2)); 
		       pimplies q1f (pands (a_values o3))]
		  in
		  let q = 
		    (* q1(true) and q2 or q1(false) and q3 *)
		    por (pand q1t q2.a_value) (pand q1f q3.a_value)
		  in
		  post_named q, Pure (o1 @ [pre_named o], None)
	    in
	    begin match post p with
	      | None -> 
		  make_node p (If (e1, e2, e3)) q, pur
	      | Some (q,_) -> 
		  { p with desc = (If (e1, e2, e3)) }, 
		  purity (get_pre pur) q.a_value
	    end
    | AppTerm (e1, t2, kapp) ->
	let e1,p1 = purify e1 in
	let d = AppTerm (e1, t2, kapp) in
	if not (is_pure p) then
	  impure d
	else begin match e1 with
	  | {desc = Var x} when is_rec x p.info.t_env ->
	      impure d
	  | {desc = LetIn (x, e1, e2)} as f ->
	      (* lift: (let x = e1 in e2) a --> let x = e1 in (e2 a) *)
	      let e2_a = 
		Typing.gmake_node p.info.t_loc e2.info.t_env (label_name ())
		  (AppTerm (e2, t2, kapp)) (result_type p) (effect p)
	      in
	      let d = LetIn (x, e1, e2_a) in
	      purify { p with desc = d }
	  | {desc = Expression t1} ->
	      (* collapse: (term(t1) term(t2)) --> term(t1 t2) *)
	      let t = applist t1 [t2] in
	      purify { p with desc = Expression t }
	  | _ -> match post p with
	      | Some (q,_) -> 
		  { p with desc = d }, purity [] q.a_value
	      | None -> match kapp.t_post with
		  | Some (q,_) -> 
		      make_node p (AppTerm (e1, t2, kapp)) q,
		      purity (get_pre p1) q.a_value
		  | None -> 
		      impure d
	end		      
    | AppRef (e1, x, kapp) ->
	let e1,p1 = purify e1 in
	let d = AppRef (e1, x, kapp) in
	begin match e1 with
	  | {desc=LetIn (x, e1, e2)} as f ->
	      (* lift: (let x = e1 in e2) a --> let x = e1 in (e2 a) *)
	      let e2_a = 
		Typing.gmake_node p.info.t_loc e2.info.t_env (label_name ())
		  (AppRef (e2, x, kapp)) (result_type p) (effect p)
	      in
	      purify { p with desc = LetIn (x, e1, e2_a) }
	  | _ ->
	      if not (is_pure p) then 
		impure d 
	      else begin match post p with
		| Some (q,_) -> 
		    { p with desc = d }, purity (get_pre p1) q.a_value
		| None -> match kapp.t_post with
		    | Some (q,_) -> 
			make_node p (AppRef (e1, x, kapp)) q,
			purity (get_pre p1) q.a_value
		    | None -> 
			impure d
	      end 
	end
    | Seq bl -> 
	let block_st = function
	  | Label _ | Assert _ as s -> s
	  | Statement e -> let e,_ = purify e in Statement e
	in
	impure (Seq (List.map block_st bl))
    | Loop (inv, var, e) ->
	let e,_ = purify e in
	impure (Loop (inv, var, e))
    | Lam (bl, e) ->
	let e = purify_prog e in
	impure (Lam (bl, e))
    | LetRef (x, e1, e2) ->
	let e1,_ = purify e1 in
	let e2,_ = purify e2 in
	impure (LetRef (x, e1, e2))
    | Rec (x, bl, v, var, e) ->
	let e = purify_prog e in
	impure (Rec (x, bl, v, var, e))
    | Raise (x, Some e) ->
	let e,_ = purify e in 
	impure (Raise (x, Some e))
    | Raise _ as d ->
	p, Impure
    | Try (e1, eql) ->
	let e1,_ = purify e1 in
	let eql = List.map (fun (p, e) -> (p, fst (purify e))) eql in
	impure (Try (e1, eql))
    | Var _ | Absurd | Any _ as d -> 
	p, Impure
    | Proof _ ->
	assert false (*TODO*)

and purify_prog (l,e) =
  let e,p = purify e in
  (l, put_pre e p)

(* we purify the whole program but we don't change its external spec *)
let purify (l,p) = 
  let {desc=d},_ = purify p in l, { p with desc = d }
****)


let purify p = p

