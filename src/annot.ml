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

(*i $Id: annot.ml,v 1.6 2002-11-28 16:18:34 filliatr Exp $ i*)

open Ident
open Misc
open Logic
open Util
open Ast
open Env
open Types

(* Automatic annotations *)

let default_post = anonymous Pfalse

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
	x, if a == default_post then a' else a
      in
      Some (q, List.map2 supx ql ql') 

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

let default_exns_post e =
  let xs = Effect.get_exns e in
  List.map (fun x -> x, default_post) xs
 
let while_post info b inv = 
  let _,s = decomp_boolean (post b) in
  let s = change_label b.info.label info.label s in
  let ql = default_exns_post info.kappa.c_effect in
  match inv with
    | None -> Some (anonymous s, ql)
    | Some i -> Some ({ a_value = pand i.a_value s; 
			a_name = Name (post_name_from i.a_name) }, ql)

let while_post_block env inv (phi,_,r) e = 
  let lab = e.info.label in
  let decphi = Papp (r, [phi; put_label_term env lab phi]) in
  let ql = default_exns_post (effect e) in
  match inv with
    | None -> 
	anonymous decphi, ql
    | Some i -> 
	{ a_value = pand i.a_value decphi; 
	  a_name = Name (post_name_from i.a_name) }, ql

(* misc. *)

let post_named c = { a_value = c; a_name = Name (post_name Anonymous) }

let create_postval c = Some (post_named c)

let create_post c = Some (post_named c, [])

let is_conditional p = match p.desc with If _ -> true | _ -> false

(* [extract_pre p] erase the pre-condition of [p] and returns it *)

let extract_oblig pr =
  { desc = pr.desc; info = { pr.info with obligations = [] } },
  pr.info.obligations

(* adds some pre-conditions *)

let add_oblig p1 pr =
  let o = pr.info.obligations in
  { desc = pr.desc; 
    info = { pr.info with obligations = o @ p1 } }
  
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
    (4) lift obligations up in assignements *)

let lift_oblig p = match p.desc with
  | Aff (x,e) ->
      let e1,p1 = extract_oblig e in
      change_desc (add_oblig p1 p) (Aff (x,e1))
  | TabAff (check, x, ({ desc = Expression _ } as e1), e2) ->
      let e1',p1 = extract_oblig e1 in
      let e2',p2 = extract_oblig e2 in
      change_desc (add_oblig (p1 @ p2) p) (TabAff (check,x,e1',e2'))
  | _ ->
      p

let rec normalize p =
  let env = p.info.env in
  let p = lift_oblig p in
  let k = p.info.kappa in
  match p.desc with
    | Aff (x, ({desc = Expression t} as e1)) 
      when post e1 = None && k.c_post = None ->
	let t = put_label_term env p.info.label (unref_term t) in
	let q = create_post (equality (Tvar x) t) in
	post_if_none env q p
    | If (e1, e2, e3) ->
	change_desc p (If (normalize_boolean env e1, e2, e3))
    | TabAff (_, x, ({desc=Expression t1} as e1), ({desc=Expression t2} as e2))
      when post e1 = None && post e2 = None && k.c_post = None ->
	let t1 = put_label_term env p.info.label (unref_term t1) in
	let t2 = put_label_term env p.info.label (unref_term t2) in
	let t = make_raw_store env (x, at_id x p.info.label) t1 t2 in
	let q = create_post (equality (Tvar x) t) in
	post_if_none env q p
    | While (b, invopt, var, e) ->
	let b' = normalize_boolean env b in
	let p = change_desc p (While (b', invopt, var, e)) in
	(match post p with
	   | None -> 
	       let q = while_post p.info b' invopt in
	       force_post env q p
	   | Some q ->
	       let q = post_app (change_label "" p.info.label) q in
	       force_post env (Some q) p)
    | LetRef (x, ({ desc = Expression t } as e1), e2) when post e1 = None ->
	let q = create_post (equality (Tvar Ident.result) (unref_term t)) in
	change_desc p (LetRef (x, post_if_none env q e1, e2))
    | LetIn (x, ({ desc = Expression t } as e1), e2) when post e1 = None ->
	let q = create_post (equality (Tvar Ident.result) (unref_term t)) in
	change_desc p (LetIn (x, post_if_none env q e1, e2))
    | Var _ | Expression _ | Acc _ | Aff _ | TabAcc _ | TabAff _  
    | Seq _ | Lam _ | LetIn _ | LetRef _ | Rec _ | App _ 
    | Raise _ | Try _ ->
	p

and normalize_boolean env b =
  let k = b.info.kappa in
  let give_post b q =
    { b with info = { b.info with kappa = { k with c_post = q } } }
  in
  let q = k.c_post in
  match q with
    | Some _ ->
	(* a postcondition; nothing to do *)
	give_post b (force_bool_name q)
    | None -> begin
	match b.desc with
	  | Expression c ->
	      (* expression E -> result=E *)
	      let c = equality (Tvar Ident.result) (unref_term c) in
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
	      b
      end
