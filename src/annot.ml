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

(*i $Id: annot.ml,v 1.13 2003-03-20 10:44:28 filliatr Exp $ i*)

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
  { pr with info = { pr.info with obligations = [] } },
  pr.info.obligations

(***
let extract_pre pr =
  let k = pr.info.kappa in
  { pr with info = { pr.info with kappa = { k with c_pre = [] } } },
  k.c_pre
***)

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

(*s Moving preconditions up in let-in (as obligations) *)

(***
let lift_pre_let_in p = match p.desc with
  | LetIn (x, ({ desc = Expression t } as e1), e2) 
    when post e1 = None && post e2 <> None ->
      let e'1,o1 = extract_pre e1 in
      let e'2,o2 = extract_pre e2 in
      if o1 <> [] || o2 <> [] then
	let s = tsubst_in_predicate (subst_one x (unref_term t)) in
	let o2 = List.map (asst_app s) o2 in
	add_oblig (o1 @ o2) { p with desc = LetIn (x, e'1, e'2) }
      else
	p
  | LetIn (x, e1, e2)
    when is_equality (post e1) && post e2 <> None && is_pure e1 ->
      let e'1,o1 = extract_pre e1 in
      let e'2,o2 = extract_pre e2 in
      if o1 <> [] || o2 <> [] then
	let t = get_equality_rhs (post e1) in
	let s = tsubst_in_predicate (subst_one x (unref_term t)) in
	let o2 = List.map (asst_app s) o2 in
	add_oblig (o1 @ o2) { p with desc = LetIn (x, e'1, e'2) }
      else
	p
  | _ ->
      p
***)

(*s Normalization. In this first pass, we
    (2) annotate [x := E] with [{ x = E }]
    (3) give tests the right postconditions
    (4) lift obligations up in assignements *)

let rec normalize p =
  let env = p.info.env in
  let p = lift_oblig_assign p in
  let k = p.info.kappa in
  match p.desc with
    | Aff (x, ({desc = Expression t} as e1)) 
      when post e1 = None && k.c_post = None ->
	let t = put_label_term env p.info.label (unref_term t) in
	let q = create_post (equality (Tvar x) t) in
	post_if_none env q p
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
		 make_lnode e.info.loc (If (b, e, praise_exit))
		   env [] (effect_and_exit b.info.kappa)
	       in
	       let d = 
		 Try 
		   (make_lnode p.info.loc
		      (While (make_bool bloc true env, invopt, var, body))
		      env [] (effect_and_exit k),
		    [ (exit_exn, None), make_void p.info.loc env])
	       in
	       change_desc p d

	   (* test is annotated -> postcondition is [inv and not test] *)
	   | Some _ ->
	       let p = change_desc p (While (b', invopt, var, e)) in
	       if post p = None then
		 let q = while_post p.info.loc p.info b' invopt in
		 force_post env q p
	       else 
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
    | Var _ | Expression _ | Acc _ | Aff _ | TabAcc _ | TabAff _  
    | Seq _ | Lam _ | LetIn _ | LetRef _ | Rec _ | App _ 
    | Raise _ | Try _ ->
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
	      begin  match post ne1, post ne2, post ne3 with
		| Some q1, Some q2, Some q3 ->
		    let q1t,q1f = decomp_boolean q1 in
		    let q2t,q2f = decomp_boolean q2 in
		    let q3t,q3f = decomp_boolean q3 in
		    let c = Pif (Tvar Ident.result,
				 por (pand q1t q2t) (pand q1f q3t),
				 por (pand q1t q2f) (pand q1f q3f)) in
		    let b' = change_desc b (If (ne1,ne2,ne3)) in
		    give_post b' (create_post c)
		| _ ->
		    b
	      end

(***
	  | LetIn (x, ({ desc = Expression t } as e1), e2) 
            when post e1 = None && post e2 <> None && is_pure e2 ->
	      let s = tsubst_in_predicate (subst_one x (unref_term t)) in
	      let q = optpost_app s (post e2) in
	      let blab = b.info.label in
	      let q = optpost_app (change_label e2.info.label blab) q in
	      lift_pre_let_in (give_post b q)
	  | LetIn (x, e1, e2) when is_equality (post e1) && post e2 <> None && 
            is_pure e1 && is_pure e2 ->
	      let t = get_equality_rhs (post e1) in
	      let s = tsubst_in_predicate (subst_one x (unref_term t)) in
	      let q = optpost_app s (post e2) in
	      let blab = b.info.label in
	      let q = optpost_app (change_label e1.info.label blab) q in
	      let q = optpost_app (change_label e2.info.label blab) q in
	      lift_pre_let_in (give_post b q)
***)
	  | _ -> 
	      b
      end
